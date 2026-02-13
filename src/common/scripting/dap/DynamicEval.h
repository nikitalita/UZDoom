#pragma once

#include "ZScriptDebugger.h"

#include <dap/protocol.h>
#include <dap/session.h>
#include <dap/traits.h>
#include "RuntimeEvents.h"
#include "PexCache.h"
#include "BreakpointManager.h"
#include "DebugExecutionManager.h"
#include "IdMap.h"
#include "Protocol/struct_extensions.h"

#include <thread>
#include <functional>
#include <string>
#include <dap/protocol.h>
#include <dap/session.h>

#include "Utilities.h"
#include "GameInterfaces.h"
#include "Nodes/StackFrameStateNode.h"
#include "Nodes/StateNodeBase.h"
#include "Nodes/CVarScopeStateNode.h"
#include "common/scripting/dap/Nodes/LocalScopeStateNode.h"
#include "c_commandline.h"
#include "c_dispatch.h"
#include "symbols.h"
#include "types.h"
#include "vm.h"
#include "vmintern.h"
#include "zcc_parser.h"

#include "zcc_compile_doom.h"
namespace DebugServer
{

inline void AddNodesToSet(ZCC_TreeNode *node, std::set<ZCC_TreeNode *> &nodes)
{
	if (!node || nodes.find(node) != nodes.end())
	{
		return;
	}
	if (node->NodeType == AST_Class || node->NodeType == AST_Struct)
	{
		ZCC_Struct *classNode = static_cast<ZCC_Struct *>(node);
		nodes.insert(classNode);
		AddNodesToSet(classNode->Body, nodes);
	} else if (node->NodeType == AST_Property) {
		ZCC_Property *propertyNode = static_cast<ZCC_Property *>(node);
		nodes.insert(propertyNode);
		AddNodesToSet(propertyNode->Body, nodes);
	} else if (node->NodeType == AST_MixinDef) {
		ZCC_MixinDef *mixinDefNode = static_cast<ZCC_MixinDef *>(node);
		nodes.insert(mixinDefNode);
		AddNodesToSet(mixinDefNode->Body, nodes);
	} else if (node->NodeType == AST_StateLine) {
		ZCC_StateLine *stateLineNode = static_cast<ZCC_StateLine *>(node);
		nodes.insert(stateLineNode);
		AddNodesToSet(stateLineNode->Action, nodes);
	} else {
		nodes.insert(node);
	}
	// depth first search; add all the children to the set
	// this is a tree, so we need to check both prev and next
	for (ZCC_TreeNode *child = node->SiblingPrev; child != node; child = child->SiblingPrev)
	{
		AddNodesToSet(child, nodes);
	}
	for (ZCC_TreeNode *child = node->SiblingNext; child != node; child = child->SiblingNext)
	{
		AddNodesToSet(child, nodes);
	}

}

inline dap::ResponseOrError<dap::EvaluateResponse> DoDynamicEval(const std::string &expression, VMFrame *frame, std::shared_ptr<PexCache> m_pexCache)
{
	if (!frame)
	{
		RETURN_DAP_ERROR(StringFormat("Could not evaluate expression %s, no frame provided", expression.c_str()).c_str());
	}
	// try to parse the expression
	std::string expression_to_parse = expression;
	// add a semicolon to the end of the expression if it doesn't already have one
	if (expression_to_parse.back() != ';')
	{
		expression_to_parse += ";";
	}
	// doing this because the zccparser expects a class name
	static constexpr const char *const fake_class = "class FAKEEXPRESSIONCLASS { static uint FAKEEXPRESSIONFUNC(ActorList currPath) { return %s } }";
	expression_to_parse = StringFormat(fake_class, expression_to_parse.c_str());
	ZCCParseState state;
	std::set<ZCC_TreeNode *> nodes;
	state.ParseVersion = MakeVersion(4, 15, 0);
	ParseSingleExpression(expression_to_parse.c_str(), state);
	if (!state.TopNode || state.TopNode->NodeType != AST_Class)
	{
		RETURN_DAP_ERROR(StringFormat("Could not parse expression %s", expression.c_str()).c_str());
	}
	AddNodesToSet(state.TopNode, nodes);
	// for (auto node : nodes)
	// {
	// 	if (node->NodeType == AST_Class)
	// 	{
	// 		ZCC_Class *classNode = (ZCC_Class *)node;
	// 		if (classNode->ParentName)
	// 		{
	// 			AddNodesToSet(classNode->ParentName, nodes);
	// 		}
	// 	}
	// }
	// pop the class off the stack
	PNamespace *parentNamespace;
	auto currscriptFunc = GetVMScriptFunction(frame->Func);
	if (!currscriptFunc)
	{
		RETURN_DAP_ERROR(StringFormat("Could not find script function for expression %s", expression.c_str()).c_str());
	}
	auto scriptName = currscriptFunc->SourceFileName;
	auto script = m_pexCache->GetScript(scriptName.GetChars());
	if (!script)
	{
		RETURN_DAP_ERROR(StringFormat("Could not find script %s for expression %s", scriptName.GetChars(), expression.c_str()).c_str());
	}
	// get the namespace by getting the archive name
	int scriptLump = script->GetScriptLump();
	int containerLump = fileSystem.GetFileContainer(scriptLump);
	int nsnum = containerLump;
	for (auto &ns : Namespaces.AllNamespaces)
	{
		if (ns->FileNum == nsnum)
		{
			parentNamespace = ns;
			break;
		}
	}
	PNamespace newns(INT_MAX, parentNamespace);
	PSymbolTable &symtable = newns.Symbols;
	int lump = 0;

	ZCCDoomCompiler cc(state, NULL, symtable, &newns, lump, state.ParseVersion);
	int error_count = cc.Compile();
	if (error_count > 0)
	{
		RETURN_DAP_ERROR(StringFormat("Could not compile expression %s", expression.c_str()).c_str());
	}

	FunctionBuildList.Build();
	FName class_name("FAKEEXPRESSIONCLASS");
	FName func_name("FAKEEXPRESSIONFUNC");
	// get the top symbol from the symbol table
	auto it = symtable.GetIterator();
	TMap<FName, PSymbol *>::Pair *pair;
	PClass *pclass = PClass::FindClass(class_name);
	if (!pclass)
	{
		RETURN_DAP_ERROR(StringFormat("Could not find class FAKEEXPRESSIONCLASS for expression %s", expression.c_str()).c_str());
	}
	auto *func = pclass->FindSymbol(func_name, false);
	if (!func)
	{
		RETURN_DAP_ERROR(StringFormat("Could not find function FAKEEXPRESSIONFUNC for expression %s", expression.c_str()).c_str());
	}
	PFunction *func_impl = (PFunction *)func;
	VMFunction *func_impl_impl = func_impl->Variants[0].Implementation;
	VMScriptFunction *scriptFunc = dynamic_cast<VMScriptFunction *>(func_impl_impl);
	VMOP *code = scriptFunc->Code;
	auto localsState = GetLocalsState(frame);
	TArray<VMValue> params;
	for (auto &local : localsState.m_locals)
	{
		VMValue value;
		if (local.Name == "self")
		{
			value = local.Value;
			DObject *self = (DObject *)value.a;
			auto ptr = self->ScriptVar(FName("currPath"), nullptr);
			value = *static_cast<VMValue *>(ptr);
			params.Push(value);
			break;
		}
	}
	VMReturn ret;
	try
	{
		VMExec(func_impl_impl, params.Data(), 1, &ret, 1);
	}
	catch (CVMAbortException &e)
	{
		RETURN_DAP_ERROR(StringFormat("Could not evaluate expression %s", expression.c_str()).c_str());
	}
	// do stuff, then...
	int j = 0;
	bool deleted = false;
	for (size_t i = 0; i < VMFunction::AllFunctions.Size(); i++)
	{
		auto &f = VMFunction::AllFunctions[i];
		if (f == func_impl_impl)
		{
			VMFunction::AllFunctions.Delete(i);
			deleted = true;
			break;
		}
	}
	if (!deleted)
	{
		RETURN_DAP_ERROR(StringFormat("Could not find function FAKEEXPRESSIONFUNC for expression %s", expression.c_str()).c_str());
	}
	pclass->VMType->Symbols.RemoveSymbol(func);
	// TODO: Not sure if we can delete the class here, or if it'll cause issues
	// instead, just make it tentative
	pclass->Size = TentativeClass;
	delete func_impl_impl;
	int i = 0;
	// dap::EvaluateResponse response;
	// response.result = ret.a;
	// return response;
	// TODO: actually return the result
	return dap::Error(StringFormat("Could not evaluate expression %s", expression.c_str()).c_str());
}
} // namespace DebugServer