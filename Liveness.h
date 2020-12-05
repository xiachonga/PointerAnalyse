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
        if (isa<Function>(V) || isa<AllocaInst>(V))
            return {V};
        return PointToSet[V];
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
    void computePhiNode(PHINode *phiNode, PointerSetInfo *dfval)
    {
        for (Use &U : phiNode->incoming_values())
        {
            ValueSetType possibleValues = dfval->getPossibleValues(U.get());
#ifdef DEBUG
            if (possibleValues.size() != 0)
                (*possibleValues.begin())->dump();
#endif
            (*dfval)[phiNode].insert(possibleValues.begin(), possibleValues.end());
        }
    }

    void computeStoreInst(StoreInst *storeInst, PointerSetInfo *dfval)
    {
        Value *valueOp = storeInst->getValueOperand();
        ValueSetType possibleValues = dfval->getPossibleValues(valueOp);
        Value *pointerOp = storeInst->getPointerOperand();
        ValueSetType possiblePointers = dfval->getPossibleValues(pointerOp);

        PointToSetType &pointToSet = dfval->PointToSet;

        if (possiblePointers.size() == 1)
        {
            Value *pointer = *possiblePointers.begin();
            pointToSet[pointer] = possibleValues;
            return;
        }
        for (Value *pointer : possiblePointers)
        {
            pointToSet[pointer].insert(possibleValues.begin(), possibleValues.end());
        }
    }

    void computeLoadInst(LoadInst *loadInst, PointerSetInfo *dfval)
    {
        Value *pointerOp = loadInst->getPointerOperand();
        ValueSetType possiblePointers = dfval->getPossibleValues(pointerOp);

        PointToSetType &pointToSet = dfval->PointToSet;
        for (Value *pointer : possiblePointers)
        {
            ValueSetType possibleValues = (*dfval)[pointer];
            pointToSet[loadInst].insert(possibleValues.begin(), possibleValues.end());
        }
    }

    void computeAllocaInst(AllocaInst *allocaInst, PointerSetInfo *dfval)
    {
    }

    void computeBitCastInst(BitCastInst *bitCastInst, PointerSetInfo *dfval)
    {
        //bitCastInst->dump();
        Value *valueOp = bitCastInst->getOperand(0);
        ValueSetType possibleValues = dfval->getPossibleValues(valueOp);
        if (CallInst *callInst = dyn_cast<CallInst>(valueOp))
        {
            (*dfval)[callInst] = {}; // FIX ME
        }
        (*dfval)[bitCastInst] = possibleValues;
    }

    void computeGetElementPtrInst(GetElementPtrInst *getElementPtrInst, PointerSetInfo *dfval)
    {
        PointToSetType &pointToSet = dfval->PointToSet;
        Value *pointerOp = getElementPtrInst->getPointerOperand();
#ifdef DEBUG
        errs() << "=========PtrInst begin========"
               << "\n";
        pointerOp->dump();
        errs() << "=========PtrInst end========"
               << "\n";
#endif
        pointToSet[getElementPtrInst] = dfval->getPossibleValues(pointerOp);
    }

    void addArgument(Function *func, PointerSetInfo &currentInfo, Value *arg, ValueSetType possibleValues)
    {
        functionArgPointSet[func][arg].insert(possibleValues.begin(), possibleValues.end());
        for (Value *value : possibleValues)
        {
            if (value == arg)
                continue;
            addArgument(func, currentInfo, value, currentInfo[value]);
        }
    }

    void computeCallInst(CallInst *callInst, PointerSetInfo *dfval)
    {
        Value *value = callInst->getCalledValue();
        ValueSetType possibleFunctions = dfval->getPossibleValues(value);
        for (Value *temp : possibleFunctions)
        {
            Function *func = dyn_cast<Function>(temp);
            assert(func && "the temp must be a function!");
            if (func->isIntrinsic())
            {
                return;
            }
            finalResult[callInst].insert(func);

            (*dfval)[callInst].insert(returnPointSet[callInst].begin(), returnPointSet[callInst].end());
            // We must get a return value from malloc, just use callinst?
            // Fix me
            if (func->getName() == "malloc")
            {
                (*dfval)[callInst] = {callInst};
                return;
            }
            functionWorkList.insert(func);
            if (callfunction.count(func) == 0)
            {
                callfunction[func] = {callInst};
            }
            else
            {
                callfunction[func].insert(callInst);
            }
            int i = 0;
            for (Use &U : callInst->args())
            {
                Value *V = U.get();
                Argument *arg = func->getArg(i);
                addArgument(func, *dfval, arg, dfval->getPossibleValues(V));
                ++i;
            }
        }
    }

    void computeReturnInst(ReturnInst *returnInst, PointerSetInfo *dfval)
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
                    if (dfval->PointToSet.count(returnValue) != 0)
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
                        ValueSetType tempReturnValueSet = dfval->PointToSet[returnValue];
                        //(*tempReturnValueSet.begin())->dump();
                        //dfval->PointToSet[*iter].insert(tempReturnValueSet.begin(), tempReturnValueSet.end());
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
        if (isa<DbgInfoIntrinsic>(inst))
            return;
        // errs() << ">>>>>>>>>>\t";
        // inst->dump();
        if (PHINode *phiNode = dyn_cast<PHINode>(inst))
        {
#ifdef DEBUG
            errs() << phiNode->getName() << "\n";
#endif
            computePhiNode(phiNode, dfval);
        }
        else if (StoreInst *storeInst = dyn_cast<StoreInst>(inst))
        {
#ifdef DEBUG
            errs() << storeInst->getName() << "\n";
#endif
            computeStoreInst(storeInst, dfval);
        }
        else if (LoadInst *loadInst = dyn_cast<LoadInst>(inst))
        {
#ifdef DEBUG
            errs() << loadInst->getName() << "\n";
#endif
            computeLoadInst(loadInst, dfval);
        }
        else if (CallInst *callInst = dyn_cast<CallInst>(inst))
        {
#ifdef DEBUG
            errs() << "===CallInst===" << callInst->getName() << "\n";
#endif
            computeCallInst(callInst, dfval);
        }
        else if (ReturnInst *returnInst = dyn_cast<ReturnInst>(inst))
        { // call 和 return都会令目标基本块的值发生改变，现在还没想好怎么弄
#ifdef DEBUG
            errs() << "===ReturnInst===" << returnInst->getName() << "\n";
#endif
            computeReturnInst(returnInst, dfval);
        }
        else if (GetElementPtrInst *getElementPtrInst = dyn_cast<GetElementPtrInst>(inst))
        {
#ifdef DEBUG
            errs() << "===GetElementPtrInst===" << getElementPtrInst->getName() << "\n";
#endif
            computeGetElementPtrInst(getElementPtrInst, dfval);
        }
        else if (AllocaInst *allocaInst = dyn_cast<AllocaInst>(inst))
        {
            computeAllocaInst(allocaInst, dfval);
        }
        else if (BitCastInst *bitCastInst = dyn_cast<BitCastInst>(inst))
        {
            computeBitCastInst(bitCastInst, dfval);
        }
        else
        {
#ifdef DEBUG
            errs() << inst->getName() << "\n";
#endif
        }
        //dfval->LiveVars.erase(inst);
        /*for(User::op_iterator oi = inst->op_begin(), oe = inst->op_end();
            oi != oe; ++oi) {
           Value * val = *oi;
           if (isa<Instruction>(val)) 
               dfval->LiveVars.insert(cast<Instruction>(val));
       }*/
    }
};

