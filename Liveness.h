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
#include <queue>

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
    map<Value *, Value *> BBStoreMap;

    PointerSetInfo() : PointToSet() {}
    PointerSetInfo(const PointerSetInfo &info) : PointToSet(info.PointToSet) {}

    inline ValueSetType getPossibleValues(Value *V)
    {
        if (isa<Function>(V) || isa<AllocaInst>(V))
            return {V};
        if (CallInst *callInst = dyn_cast<CallInst>(V))
            if (Function *func = dyn_cast<Function>(callInst->getCalledValue()))
                if (func->getName() == "malloc")
                {
                    return {V};
                }
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

    ValueSetType getPossiblePointedValues(Value *V)
    {
        if (BBStoreMap.count(V))
            return PointToSet[BBStoreMap[V]];
        ValueSetType possiblePointers = getPossibleValues(V);
        ValueSetType possiblePointedValues;
        for (Value *pointer : possiblePointers)
        {
            possiblePointedValues.insert(PointToSet[pointer].begin(), PointToSet[pointer].end());
        }
        return possiblePointedValues;
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

class PointToSetVisitor : public DataflowVisitor<struct PointerSetInfo>
{
private:
    queue<Function *> functionWorkQueue;
    map<CallInst *, set<Function *>> finalResult;

    map<Function *, PointerSetInfo> functionArgPointSet;
    map<Function *, PointerSetInfo> functionRetPointSet;
    map<Function *, set<Function *>> functionRetWakeupFunctions;

    bool pass = false;

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
    PointToSetVisitor() : functionWorkQueue() {}
    queue<Function *> &getFunctionWorkQueue()
    {
        return functionWorkQueue;
    }

    void reset()
    {
        functionWorkQueue = {};
        pass = false;
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
        if (pass)
            return;
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

    void store(Value *inst, PointerSetInfo &info, Value *pointerOp, ValueSetType &possibleValues)
    {
        info.BBStoreMap[pointerOp] = inst;
        info[inst] = possibleValues;
        ValueSetType possiblePointers = info.getPossibleValues(pointerOp);
        if (possiblePointers.size() == 1)
        {
            Value *pointer = *possiblePointers.begin();
            info[pointer] = possibleValues;
            return;
        }
        for (Value *pointer : possiblePointers)
        {
            if (info.BBStoreMap.count(pointer))
                info.BBStoreMap.erase(pointer);
            info[pointer].insert(possibleValues.begin(), possibleValues.end());
        }
    }

    void computeStoreInst(StoreInst *storeInst, PointerSetInfo &info)
    {
        Value *valueOp = storeInst->getValueOperand();
        ValueSetType possibleValues = info.getPossibleValues(valueOp);
        Value *pointerOp = storeInst->getPointerOperand();
        store(storeInst, info, pointerOp, possibleValues);
    }

    void computeLoadInst(LoadInst *loadInst, PointerSetInfo &info)
    {
        Value *pointerOp = loadInst->getPointerOperand();
        info[loadInst] = info.getPossiblePointedValues(pointerOp);
    }

    void computeMemCpyInst(MemCpyInst *memCpyInst, PointerSetInfo &info)
    {
        Value *dst = memCpyInst->getArgOperand(0);
        Value *src = memCpyInst->getArgOperand(1);
        ValueSetType possibleValues = info.getPossiblePointedValues(src);
        store(memCpyInst, info, dst, possibleValues);
    }

    void computeBitCastInst(BitCastInst *bitCastInst, PointerSetInfo &info)
    {
        Value *valueOp = bitCastInst->getOperand(0);
        info[bitCastInst] = info.getPossibleValues(valueOp);
    }

    void computeGetElementPtrInst(GetElementPtrInst *getElementPtrInst, PointerSetInfo &info)
    {
        Value *pointerOp = getElementPtrInst->getPointerOperand();
        info[getElementPtrInst] = info.getPossibleValues(pointerOp);
    }

    void movePointerSetInfo(PointerSetInfo &dst, PointerSetInfo &src, Value *pointer, bool replace = false)
    {
        if (replace)
            dst[pointer] = src[pointer];
        else
            dst[pointer].insert(src[pointer].begin(), src[pointer].end());
        for (Value *value : src[pointer])
        {
#ifdef DEBUG
            assert(value != pointer && "value and pointer must be different!");
#else
            if (value == pointer)
                continue;
#endif
            replace = replace && src[pointer].size() <= 1;
            movePointerSetInfo(dst, src, value, replace);
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
            if (func->getName() == "malloc")
                return;
            // add argument
            PointerSetInfo newInfo = functionArgPointSet[func];
            int argc = 0;
            for (Use &U : callInst->args())
            {
                Value *V = U.get();
                Argument *arg = func->getArg(argc);
                ValueSetType possibleValues = info.getPossibleValues(V);
                if (info.BBStoreMap.count(V))
                {
                    possibleValues = {info.BBStoreMap[V]};
                }
                newInfo[arg].insert(possibleValues.begin(), possibleValues.end());
                for (Value *pointer : possibleValues)
                {
                    movePointerSetInfo(newInfo, info, pointer);
                }
                argc++;
            }
            if (newInfo == functionArgPointSet[func])
                continue;
            functionArgPointSet[func] = newInfo;
            functionWorkQueue.push(func);
            pass = true;
        }
        if (pass)
        {
            functionWorkQueue.push(callInst->getParent()->getParent());
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
                ValueSetType possibleValues = info.getPossibleValues(V);
                bool replace = possibleValues.size() == 1 && possibleFunctions.size() == 1;
                for (Value *pointer : possibleValues)
                {
                    movePointerSetInfo(info, functionRetPointSet[func], pointer, replace);
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
        for (Function *func : functionRetWakeupFunctions[parent])
        {
            functionWorkQueue.push(func);
        }
        functionRetPointSet[parent] = newInfo;
    }

    void compDFVal(Instruction *inst, PointerSetInfo *dfval) override
    {
        if (pass)
            return;
        PointerSetInfo &info = *dfval;
        if (isa<DbgInfoIntrinsic>(inst))
            return;
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
            if (MemCpyInst *memCpyInst = dyn_cast<MemCpyInst>(inst))
                computeMemCpyInst(memCpyInst, info);
            else
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
#ifdef INST
            if (inst->getParent()->getParent()->getName() == "swap_w")
            {
                errs() << ">>>!! Instruction need to handle\t";
                inst->dump();
            }
#endif
#endif
        }
    }
};
