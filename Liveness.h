//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/InstIterator.h>
#include "Dataflow.h"

#include <set>
#include <map>
using namespace llvm;

using ValueSetType = std::set<Value *>;
using PointToSetType = std::map<Value *, ValueSetType>;
using ValueValuesMapType = std::map<Value *, ValueSetType>;
using Functions = std::set<Function *>;

//#define DEBUG
struct PointerSetInfo
{
    // Point To Value Map
    // Pointer and value it points to
    PointToSetType PointToSet;

    PointerSetInfo() : PointToSet() {}
    PointerSetInfo(const PointerSetInfo &info) : PointToSet(info.PointToSet) {}

    inline ValueSetType getPossibleValues(Value *V)
    {
        // FIX ME
        // add what malloc as what allocaInst do?
        if (isa<Constant>(V) || isa<AllocaInst>(V))
            return {V};
        return PointToSet[V];
    }

    inline Functions getPossibleFuntcions(Value *V)
    {
        if (Function *func = dyn_cast<Function>(V))
            return {func};
        Functions funcs;
        for (Value *temp : PointToSet[V])
        {
            Function *func = dyn_cast<Function>(temp);
            assert(func && "The vaule must be a function!");
            funcs.insert(func);
        }
        return funcs;
    }

    ValueSetType &operator[](Value *V)
    {
        return PointToSet[V];
    }

    bool operator==(const PointerSetInfo &info) const
    {
        return PointToSet == info.PointToSet;
    }
};

inline raw_ostream &operator<<(raw_ostream &out, const PointerSetInfo &info)
{
    return out;
}

class PointToSetVisitor : public DataflowVisitor<struct PointerSetInfo>
{
private:
    std::set<Function *> functionWorkList;
    std::map<CallInst *, std::set<Function *>> finalResult;
    std::map<Function *, PointerSetInfo> functionArgPointSet;
    std::map<Function *, std::set<CallInst *>> callfunction;
    PointToSetType returnPointSet;

public:
    PointToSetVisitor() : functionWorkList() {}
    std::set<Function *> &getFunctionWorkList()
    {
        return functionWorkList;
    }
    void setFunctionWorkList(std::set<Function *> func)
    {
        this->functionWorkList = func;
    }
    std::map<Function *, PointerSetInfo> getFunctionArgPointSet()
    {
        return functionArgPointSet;
    }
    std::map<CallInst *, std::set<Function *>> getFinalResult()
    {
        return finalResult;
    }

    void merge(PointerSetInfo *dest, const PointerSetInfo &src) override
    {
        for (auto iter = src.PointToSet.begin(); iter != src.PointToSet.end(); ++iter)
        {
            if (dest->PointToSet.find(iter->first) != dest->PointToSet.end())
            {
                dest->PointToSet[iter->first].insert(iter->second.begin(), iter->second.end());
            }
            else
            {
                dest->PointToSet.insert(std::make_pair(iter->first, iter->second));
            }
        }
    }
    void computePhiNode(PHINode *phiNode, PointerSetInfo &info)
    {
        for (Use &U : phiNode->incoming_values())
        {
            ValueSetType possibleValues = info.getPossibleValues(U.get());
            info[phiNode].insert(possibleValues.begin(), possibleValues.end());
        }
    }

    void computeStoreInst(StoreInst *storeInst, PointerSetInfo &info)
    {
        Value *valueOp = storeInst->getValueOperand();
        ValueSetType possibleValues = info.getPossibleValues(valueOp);
        Value *pointerOp = storeInst->getPointerOperand();
        ValueSetType possiblePointers = info.getPossibleValues(pointerOp);

        if (possiblePointers.size() == 1)
        {
            Value *pointer = *possiblePointers.begin();
            info[pointer] = possibleValues;
            return;
        }
        for (Value *pointer : possiblePointers)
        {
            info[pointer].insert(possibleValues.begin(), possibleValues.end());
        }
    }

    void computeLoadInst(LoadInst *loadInst, PointerSetInfo &info)
    {
        Value *pointerOp = loadInst->getPointerOperand();
        ValueSetType possiblePointers = info.getPossibleValues(pointerOp);

        for (Value *pointer : possiblePointers)
        {
            ValueSetType possibleValues = info[pointer];
            info[loadInst].insert(possibleValues.begin(), possibleValues.end());
        }
    }

    void computeBitCastInst(BitCastInst *bitCastInst, PointerSetInfo &info)
    {
        Value *valueOp = bitCastInst->getOperand(0);
        ValueSetType possibleValues = info.getPossibleValues(valueOp);
        if (CallInst *callInst = dyn_cast<CallInst>(valueOp))
        {
            if (Function *fmalloc = dyn_cast<Function>(callInst->getCalledValue()))
            {
                if (fmalloc->getName() == "malloc")
                {
                    // FIX ME
                    // just use the callinst as the malloc return value
                    // in llvm, we can create "malloc" IR with createMalloc in class CallInst
                    info[bitCastInst] = {valueOp};
                    return;
                }
            }
        }
        valueOp->dump();
        assert(0 && ">>>>> computeBitCastInst: operand not a malloc value!");
    }

    void computeGetElementPtrInst(GetElementPtrInst *getElementPtrInst, PointerSetInfo &info)
    {
        Value *pointerOp = getElementPtrInst->getPointerOperand();
        info[getElementPtrInst] = info.getPossibleValues(pointerOp);
    }

    void addArgument(PointerSetInfo &argsInfo, PointerSetInfo &currentInfo, Value *arg, ValueSetType possibleValues)
    {
        argsInfo[arg].insert(possibleValues.begin(), possibleValues.end());
        for (Value *value : possibleValues)
        {
            if (value == arg)
                continue;
            addArgument(argsInfo, currentInfo, value, currentInfo[value]);
        }
    }

    void computeCallInst(CallInst *callInst, PointerSetInfo &info)
    {
        Value *value = callInst->getCalledValue();
        Functions possibleFunctions = info.getPossibleFuntcions(value);
        for (Function *func : possibleFunctions)
        {
            if (func->isIntrinsic())
                return;
            // Add function to result
            finalResult[callInst].insert(func);
            // FIX ME
            // We must get a return value from malloc, just use callinst, do it specilly in computeBitCastInst?
            if (func->getName() == "malloc")
                return;
            // get return value
            info[callInst].insert(returnPointSet[callInst].begin(), returnPointSet[callInst].end());

            functionWorkList.insert(func);
            callfunction[func].insert(callInst);
            // add argument
            int argc = 0;
            for (Use &U : callInst->args())
            {
                Value *V = U.get();
                Argument *arg = func->getArg(argc);
                addArgument(functionArgPointSet[func], info, arg, info.getPossibleValues(V));
                argc++;
            }
        }
    }

    void computeReturnInst(ReturnInst *returnInst, PointerSetInfo *info)
    {
//存函数可能有哪些callInst调用，然后根据函数找这些callInst，
#ifdef DEBUG
        errs() << "======computeReturnInst begin========"
               << "\n";
        returnInst->dump();
        returnInst->getParent()->dump();
        returnInst->getReturnValue()->dump();
        errs() << "======computeReturnInst end========"
               << "\n";
#endif
        if (Function *funcTemp = dyn_cast<Function>(returnInst->getParent()->getParent()))
        {
            if (callfunction.count(funcTemp) != 0)
            {
                std::set<CallInst *> tempCallSet = callfunction[funcTemp];
                Value *returnValue = returnInst->getReturnValue();
                for (std::set<CallInst *>::iterator iter = tempCallSet.begin(); iter != tempCallSet.end(); ++iter)
                {
                    if (info->PointToSet.count(returnValue) != 0)
                    {
#ifdef DEBUG
                        errs() << "======returnFunction begin======"
                               << "\n";
                        funcTemp->dump();
                        (*iter)->dump();
                        returnValue->dump();
                        errs() << "======returnFunction end======"
                               << "\n";
#endif
                        ValueSetType tempReturnValueSet = info->PointToSet[returnValue];
                        //(*tempReturnValueSet.begin())->dump();
                        //info->PointToSet[*iter].insert(tempReturnValueSet.begin(), tempReturnValueSet.end());
                        unsigned int size = returnPointSet[*iter].size();
                        //errs() << size << "\n";
                        returnPointSet[*iter].insert(tempReturnValueSet.begin(), tempReturnValueSet.end());
                        //errs() << returnPointSet[*iter].size() <<"\n";
                        if (size != returnPointSet[*iter].size())
                        { //TODO
                            if (Function *recomputeFunction = dyn_cast<Function>((*iter)->getParent()->getParent()))
                            {
                                //recomputeFunction->dump();
                                functionWorkList.insert(recomputeFunction);
                            }
                        }
                    }
                }
            }
        }
        return;
    }

    void compDFVal(Instruction *inst, PointerSetInfo *dfval) override
    {
        PointerSetInfo &info = *dfval;
        if (isa<DbgInfoIntrinsic>(inst))
            return;
#ifdef INFO
        errs() << ">>>>> compDFVal\t";
        inst->dump();
#endif
        if (PHINode *phiNode = dyn_cast<PHINode>(inst))
        {
            computePhiNode(phiNode, info);
        }
        else if (StoreInst *storeInst = dyn_cast<StoreInst>(inst))
        {
            computeStoreInst(storeInst, info);
        }
        else if (LoadInst *loadInst = dyn_cast<LoadInst>(inst))
        {
            computeLoadInst(loadInst, info);
        }
        else if (CallInst *callInst = dyn_cast<CallInst>(inst))
        {
            computeCallInst(callInst, info);
        }
        else if (ReturnInst *returnInst = dyn_cast<ReturnInst>(inst))
        { // call 和 return都会令目标基本块的值发生改变，现在还没想好怎么弄
            computeReturnInst(returnInst, &info);
        }
        else if (GetElementPtrInst *getElementPtrInst = dyn_cast<GetElementPtrInst>(inst))
        {
            computeGetElementPtrInst(getElementPtrInst, info);
        }
#ifdef DEBUG
        else if (AllocaInst *allocaInst = dyn_cast<AllocaInst>(inst))
        {

            errs() << ">>>>> AllocaInst\t";
            allocaInst->dump();
        }
#endif
        else if (BitCastInst *bitCastInst = dyn_cast<BitCastInst>(inst))
        {
            computeBitCastInst(bitCastInst, info);
        }
        else
        {
#ifdef DEBUG
            errs() << ">>>!! Instruction need to handle\t";
            inst->dump();
#endif
        }
    }
};
