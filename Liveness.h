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
struct LivenessInfo {
   std::set<Instruction *> LiveVars;             /// Set of variables which are live

   // Point To Value Map
   // Pointer and value it points to
   PointToSetType PointToSet;
   // Possible Value Map
   // A instruction (phiNode or load) have more than one possible result
   // An argument that has more than one possible value
   std::map<Value *, std::set<Value *>> PVM;

   LivenessInfo() : PointToSet() {}
   LivenessInfo(const LivenessInfo & info) : PointToSet(info.PointToSet) {}
  
   bool operator == (const LivenessInfo & info) const {
       return PointToSet == info.PointToSet;
   }
};

inline raw_ostream &operator<<(raw_ostream &out, const LivenessInfo &info) {
    for (std::set<Instruction *>::iterator ii=info.LiveVars.begin(), ie=info.LiveVars.end();
         ii != ie; ++ ii) {
       const Instruction * inst = *ii;
       out << inst->getName();
       out << " ";
    }
    return out;
}

	
class LivenessVisitor : public DataflowVisitor<struct LivenessInfo> {
private:
    std::set<Function* > functionWorkList;
    std::map<CallInst*, std::set<Function*> > finalResult;
    std::map<Function*, LivenessInfo> functionArgPointSet;
    std::map<Function*, std::set<CallInst*> > callfunction;
    PointToSetType returnPointSet;
public:
   LivenessVisitor(): functionWorkList(){}
   std::set<Function* > &getFunctionWorkList() {
       return functionWorkList;
   }
   void setFunctionWorkList(std::set<Function* > func) {
       this->functionWorkList = func;
   }
   std::map<Function*, LivenessInfo> getFunctionArgPointSet() {
       return functionArgPointSet;
   }
   std::map<CallInst*, std::set<Function*> > getFinalResult() {
       return finalResult;
   }
   void merge(LivenessInfo * dest, const LivenessInfo & src) override {
       for(auto iter = src.PointToSet.begin(); iter != src.PointToSet.end(); ++iter) {
           if (dest->PointToSet.find(iter->first) != dest->PointToSet.end()) {
               dest->PointToSet[iter->first].insert(iter->second.begin(), iter->second.end());
           } else {
               dest->PointToSet.insert(std::make_pair(iter->first, iter->second));
           }
       }
   }
   void computePhiNode(PHINode* phiNode, LivenessInfo* dfval) {
       ValueSetType valueTempSet = {};
       for (Use &U : phiNode->incoming_values()) {
            //U.get()->dump();
            valueTempSet.insert(U.get());
		}
        //dfval->PointToSet.insert(std::make_pair(phiNode, valueTempSet));
        dfval->PointToSet[phiNode] = valueTempSet;
       return;
   }

   void computeStoreInst(StoreInst* storeInst, LivenessInfo* dfval) {
/* 
     Value *value = storeInst->getValueOperand();  // Value to store
     Value *pointer = storeInst->getPointerOperand(); // Address where to store
     PointToSetType &pointToSet = dfval->PointToSet;
     ValueValuesMapType &PVM = dfval->PVM;
     if (pointToSet[pointer].size() == 1) {
       Value *pointedValue = *pointToSet[pointer].begin();
       PVM[pointedValue] = PVM[value];
       return;
     }
     for (Value *pointedValue : pointToSet[pointer]) {
       PVM[pointedValue].insert(PVM[value].begin(), PVM[value].end());
     }
*/
     errs() << ">>>>> store\n";
     storeInst->dump();
     Value *value = storeInst->getValueOperand();
     Value *pointer = storeInst->getPointerOperand();
     PointToSetType &pointToSet = dfval->PointToSet;
     if (pointToSet[pointer].size() == 1) {
       Value *pointerValue = *pointToSet[pointer].begin();
       pointToSet[pointerValue] = {value};
       return;
     }
     for (Value *pointerValue : pointToSet[pointer]){
       pointToSet[pointerValue].insert(value);
     }

   }

   void computeLoadInst(LoadInst* loadInst, LivenessInfo* dfval) {
/*     Value *pointer = storeInst->getPointerOperand(); // Address where load from
     ValueValuesMapType &PVM = dfval->PVM;
     for (Value *pointedValue : pointToSet[pointer]){
       PVM[loadInst].insert(PVM[pointedValue].begin(), PVM[pointedValue].end());
     }
*/
     errs() << ">>>>> load\n";
     loadInst->dump();
       Value *pointer = loadInst->getPointerOperand();
       PointToSetType &pointToSet = dfval->PointToSet;
       pointToSet[loadInst] = {};
       ValueSetType &valueSet = pointToSet[loadInst];
       for (Value *pointerValue : pointToSet[pointer]) {
         valueSet.insert(pointToSet[pointerValue].begin(), pointToSet[pointerValue].end());
       }
   }

   void handleFunctionArgs(CallInst* callInst, Function* func, LivenessInfo* dfval) {
        int i = 0;
        for (Use& U : callInst->args()) {
            if (Function * funcArg = dyn_cast<Function>(U.get())) { 
                #ifdef DEBUG
                U.get()->dump();
                errs() << funcArg->getName()<<"\n";
                func->getArg(i)->dump();
                #endif
                Argument * arg = func->getArg(i);
                if (functionArgPointSet.count(func) == 0) { //add {func, {arg, {funcArg}}}
                    ValueSetType pointSet = {funcArg};
                    LivenessInfo info;
                    info.PointToSet.insert(std::make_pair(arg, pointSet)); 
                    functionArgPointSet.insert(std::make_pair(func, info)); 
                } else {
                    functionArgPointSet[func].PointToSet[arg].insert(funcArg);
                }
                   
            } else {
                #ifdef DEBUG 
                errs()<<"=======else======"<<"\n";
                U.get()->dump();
                #endif
                if (dfval->PointToSet.count(U.get()) != 0) {
                    ValueSetType pointSet = dfval->PointToSet[U.get()];
                    Argument * arg = func->getArg(i);
                    if (functionArgPointSet.count(func) == 0) { //add {func, {arg, {funcArg}}}
                        LivenessInfo info;
                        info.PointToSet.insert(std::make_pair(arg, pointSet)); 
                        functionArgPointSet.insert(std::make_pair(func, info)); 
                    } else {
                        functionArgPointSet[func].PointToSet[arg].insert(pointSet.begin(), pointSet.end());
                    }
                }
            }
            ++i;
        } 
       return;
   } 
   void computeCallInst(CallInst* callInst, LivenessInfo* dfval) {
       Value* value = callInst->getCalledValue();
       //value->dump();
       
       if (Function* func = dyn_cast<Function>(value)) {
           if (func->isIntrinsic()) {
               return;
           }
           std::set<Function* > funcSet = {func};
           functionWorkList.insert(func);
           finalResult.insert(std::make_pair(callInst, funcSet));
           if (callfunction.count(func) == 0) {
               callfunction[func] = {callInst};
           } else {
               callfunction[func].insert(callInst);
           }    
           handleFunctionArgs(callInst, func, dfval);

       } else {
           #ifdef DEBUG
           errs() << "value is a function pointer" << "\n";
           value->dump();
           #endif
           dfval->PointToSet[value].insert(returnPointSet[value].begin(), returnPointSet[value].end());
           if (dfval->PointToSet.count(value) != 0) {
               std::set<Function* > funcSet = {};
               ValueSetType PointSet = dfval->PointToSet[value];
               for(ValueSetType::iterator iter = PointSet.begin(); iter != PointSet.end(); ++iter) {
                   if (Function* funcTemp = dyn_cast<Function>(*iter)) {
                       #ifdef
                       errs() << "=============" << "\n";
                       funcTemp->dump();
                       #endif
                       functionWorkList.insert(funcTemp);
                       funcSet.insert(funcTemp);
                       if (callfunction.count(funcTemp) == 0) {
                            callfunction[funcTemp] = {callInst};
                        } else {
                            callfunction[funcTemp].insert(callInst);
                        } 
                       handleFunctionArgs(callInst, funcTemp, dfval);
                   }
               }
               finalResult[callInst] = funcSet;
           }
       }
       return;
   } 
   void computeReturnInst(ReturnInst* returnInst, LivenessInfo* dfval) {
       //存函数可能有哪些callInst调用，然后根据函数找这些callInst，
       #ifdef DEBUG
       errs() << "======computeReturnInst begin========" <<"\n";
       returnInst->dump();
       returnInst->getParent()->dump();
       returnInst->getReturnValue()->dump();
       errs() << "======computeReturnInst end========" <<"\n";
       #endif
       if (Function* funcTemp = dyn_cast<Function>(returnInst->getParent()->getParent())) {
           if (callfunction.count(funcTemp) != 0) {
               std::set<CallInst* > tempCallSet = callfunction[funcTemp];
               Value* returnValue = returnInst->getReturnValue();
               for(std::set<CallInst* >::iterator iter = tempCallSet.begin(); iter != tempCallSet.end(); ++iter) {
                   if (dfval->PointToSet.count(returnValue) != 0) {
                       errs() <<"======returnFunction begin======"<<"\n";
                       funcTemp->dump();
                       (*iter)->dump();
                       errs() <<"======returnFunction end======"<<"\n";
                       ValueSetType tempReturnValueSet = dfval->PointToSet[returnValue];
                       (*tempReturnValueSet.begin())->dump();
                       //dfval->PointToSet[*iter].insert(tempReturnValueSet.begin(), tempReturnValueSet.end());
                       unsigned int size = returnPointSet[*iter].size();
                       errs() << size << "\n";
                       returnPointSet[*iter].insert(tempReturnValueSet.begin(), tempReturnValueSet.end());
                       errs() << returnPointSet[*iter].size() <<"\n";
                       if (size != returnPointSet[*iter].size()) { //TODO
                            if (Function* recomputeFunction = dyn_cast<Function>((*iter)->getParent()->getParent())) {
                                recomputeFunction->dump();
                                functionWorkList.insert(recomputeFunction);
                            }
                       }
                   }
               }
           }
       }
       return;
   }

   void computeAllocaInst(AllocaInst *allocaInst, LivenessInfo *dfval) {
     PointToSetType &pointToSet = dfval->PointToSet;
     pointToSet[allocaInst] = {};
   }

   void computeGetElementPtrInst(GetElementPtrInst* getElementPtrInst, LivenessInfo* dfval) {
     errs() << ">>>>> ptr\n";
     getElementPtrInst->dump();
     PointToSetType &pointToSet = dfval->PointToSet;
     Value *pointer = getElementPtrInst->getPointerOperand();
     if (isa<AllocaInst>(pointer))
       pointToSet[getElementPtrInst] = {getElementPtrInst->getPointerOperand()};
     else {
       pointToSet[getElementPtrInst] = pointToSet[pointer];
     }
   }
   void compDFVal(Instruction *inst, LivenessInfo * dfval) override{
        if (isa<DbgInfoIntrinsic>(inst)) return;
//        inst->dump();
        if (PHINode* phiNode = dyn_cast<PHINode>(inst)) {
            #ifdef DEBUG
                errs() << phiNode->getName() << "\n";
            #endif
            computePhiNode(phiNode, dfval);
        } else if (StoreInst* storeInst = dyn_cast<StoreInst>(inst)) {
            #ifdef DEBUG
                errs() << storeInst->getName() << "\n";
            #endif
            computeStoreInst(storeInst, dfval);
        } else if (LoadInst* loadInst = dyn_cast<LoadInst>(inst)) {
            #ifdef DEBUG
                errs() << loadInst->getName() << "\n";
            #endif
            computeLoadInst(loadInst, dfval);
        } else if (CallInst* callInst = dyn_cast<CallInst>(inst)) {
            #ifdef DEBUG
                errs() << "===CallInst===" << callInst->getName() << "\n";
            #endif
            computeCallInst(callInst, dfval);
        } else if (ReturnInst* returnInst = dyn_cast<ReturnInst>(inst)) { // call 和 return都会令目标基本块的值发生改变，现在还没想好怎么弄
            #ifdef DEBUG
                errs() << "===ReturnInst===" << returnInst->getName() << "\n";
            #endif
            computeReturnInst(returnInst, dfval);
        } else if (GetElementPtrInst* getElementPtrInst = dyn_cast<GetElementPtrInst>(inst)) {
            #ifdef DEBUG
                errs() << "===GetElementPtrInst===" << getElementPtrInst->getName() << "\n";
            #endif
            computeGetElementPtrInst(getElementPtrInst, dfval);
        } else if (AllocaInst *allocaInst = dyn_cast<AllocaInst>(inst)){
          computeAllocaInst(allocaInst, dfval);
        } else {
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


class Liveness : public FunctionPass {
public:

   static char ID;
   Liveness() : FunctionPass(ID) {} 

   bool runOnFunction(Function &F) override {
       //F.dump();
       LivenessVisitor visitor;
       DataflowResult<LivenessInfo>::Type result;
       LivenessInfo initval;

       compBackwardDataflow(&F, &visitor, &result, initval);
       //printDataflowResult<LivenessInfo>(errs(), result);
       return false;
   }
};



