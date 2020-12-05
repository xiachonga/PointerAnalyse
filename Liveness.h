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
using namespace std;

using ValueSetType = set<Value *>;
using PointToSetType = map<Value *, ValueSetType>;
using ValueValuesMapType = map<Value *, ValueSetType>;
using Functions = set<Function *>;

// #define INST
// #define FUNC

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
            if (isa<ConstantPointerNull>(temp))
            {
#ifdef DEBUG
                errs() << ">>>>> getPossibleFuntcions: Constant Null\n";
#endif
                continue;
            }
            assert(func && "The vaule must be a function!");
            funcs.insert(func);
        }
        return funcs;
    }

    ValueSetType &operator[](Value *V)
    {
        return PointToSet[V];
    }

    bool count(Value *V)
    {
        return PointToSet.count(V);
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
    set<Function *> functionWorkList;
    map<CallInst *, set<Function *>> finalResult;

    map<Function *, PointerSetInfo> functionArgPointSet;
    map<Function *, PointerSetInfo> functionRetPointSet;
    map<Function *, set<Function *>> functionRetWakeupFunctions;

    void dumpValue(Value *V)
    {
        if (Function *F = dyn_cast<Function>(V))
            errs() << "  Function " << F->getName() << "\n";
        else if (Instruction *I = dyn_cast<Instruction>(V))
        {
            errs() << "  " << I->getParent()->getParent()->getName();
            I->dump();
        }
        else
            V->dump();
    }

public:
    PointToSetVisitor() : functionWorkList() {}
    set<Function *> &getFunctionWorkList()
    {
        return functionWorkList;
    }
    void setFunctionWorkList(set<Function *> func)
    {
        this->functionWorkList = func;
    }
    map<Function *, PointerSetInfo> &getFunctionArgPointSet()
    {
        return functionArgPointSet;
    }
    map<CallInst *, set<Function *>> getFinalResult()
    {
        return finalResult;
    }

    void merge(PointerSetInfo *dest, const PointerSetInfo &src) override
    {
        for (pair<Value *, ValueSetType> temp : src.PointToSet)
        {
            dest->PointToSet[temp.first].insert(temp.second.begin(), temp.second.end());
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
        // errs() << "!!!!!\n";
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
        info[bitCastInst] = info.getPossibleValues(valueOp);
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

    void movePointerSetInfo(PointerSetInfo &dst, PointerSetInfo &src, Value *poniter)
    {
        if (!src.count(poniter))
            return;
        dst[poniter].insert(src[poniter].begin(), src[poniter].end());
        for (Value *value : src[poniter])
        {
#ifdef DEBUG
            assert(value != poniter && "value and poniter must be different!");
#else
            if (value == poniter)
                continue;
#endif
            movePointerSetInfo(dst, src, value);
        }
    }

    void computeCallInst(CallInst *callInst, PointerSetInfo &info)
    {
        Value *value = callInst->getCalledValue();
        Functions possibleFunctions = info.getPossibleFuntcions(value);
        // deal with call
        for (Function *func : possibleFunctions)
        {
            if (func->isIntrinsic())
                return;
            // Add function to result
            finalResult[callInst].insert(func);
            functionRetWakeupFunctions[func].insert(callInst->getParent()->getParent());
            // FIX ME
            // We must get a return value from malloc, just use callinst, do it specilly in computeBitCastInst?
            if (func->getName() == "malloc")
                return;
            // add argument
            PointerSetInfo newInfo = functionArgPointSet[func];
            int argc = 0;
            // errs() << ">> Adding argument for " << func->getName() << "\n";
            for (Use &U : callInst->args())
            {
                Value *V = U.get();
                Argument *arg = func->getArg(argc);
                addArgument(newInfo, info, arg, info.getPossibleValues(V));
                argc++;
            }
            if (newInfo == functionArgPointSet[func])
                continue;
            functionArgPointSet[func] = newInfo;
            functionWorkList.insert(func);
        }
        // Deal with return
        for (Function *func : possibleFunctions)
        {
            if (func->isIntrinsic())
                return;
            // function return values
            info[callInst].insert(functionRetPointSet[func][func].begin(), functionRetPointSet[func][func].end());
            for (Value *pointer : functionRetPointSet[func][func])
            {
                movePointerSetInfo(info, functionRetPointSet[func], pointer);
            }
            // pointer arguments
            int argc = 0;
            for (Use &U : callInst->args())
            {
                Value *V = U.get();
                for (Value *pointer : info.getPossibleValues(V))
                {
                    movePointerSetInfo(info, functionRetPointSet[func], pointer);
                }
                argc++;
            }
        }
    }

    void computeReturnInst(ReturnInst *returnInst, PointerSetInfo &info)
    {
        Function *parent = returnInst->getParent()->getParent();
        PointerSetInfo newInfo = functionRetPointSet[parent];
        if (Value *returnValue = returnInst->getReturnValue())
        {
            ValueSetType possibleValue = info.getPossibleValues(returnValue);
            newInfo[parent] = possibleValue;
            for (Value *pointer : possibleValue)
                movePointerSetInfo(newInfo, info, pointer);
        }
        PointerSetInfo &argsPointerSet = functionArgPointSet[parent];
        for (size_t argc = 0; argc < parent->arg_size(); argc++)
        {
            Argument *arg = parent->getArg(argc);
            for (Value *pointer : argsPointerSet.getPossibleValues(arg))
            {
                movePointerSetInfo(newInfo, info, pointer);
            }
        }
        if (newInfo == functionRetPointSet[parent])
            return;
        // Wakeup
        functionWorkList.insert(functionRetWakeupFunctions[parent].begin(), functionRetWakeupFunctions[parent].end());
        functionRetPointSet[parent] = newInfo;
    }

    void compDFVal(Instruction *inst, PointerSetInfo *dfval) override
    {
        PointerSetInfo &info = *dfval;
        if (isa<DbgInfoIntrinsic>(inst))
            return;
#ifdef INST
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
        {
            computeReturnInst(returnInst, info);
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
#ifdef ERROR
            errs() << ">>>!! Instruction need to handle\t";
            inst->dump();
#endif
        }
    }
};
