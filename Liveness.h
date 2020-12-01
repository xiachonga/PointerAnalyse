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

//#define DEBUG
struct LivenessInfo {
   std::set<Instruction *> LiveVars;             /// Set of variables which are live
   PointToSetType PointToSet;
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
     Value *value = storeInst->getValueOperand();
     Value *pointer = storeInst->getPointerOperand();
     /*if (GetElementPtrInst *getElementPtrInst = dyn_cast<GetElementPtrInst>(pointer)){
       errs() << ">>>>> store\n";
       pointer->dump();
     PointToSetType &pointToSet = dfval->PointToSet;
     for (Value *pointerValue : pointToSet[pointer]){
       //pointToSet[pointerValue] = pointToSet[value];
       pointToSet[pointerValue].insert(value);
         errs() << pointerValue << " " << pointToSet[pointerValue].size();
       pointerValue->dump();
     }
       errs() << ">>>>>\n";
     return;
     }*/
     PointToSetType &pointToSet = dfval->PointToSet;
     if (pointToSet[pointer].size() == 1)
       pointToSet[pointerValue] = {value};
     for (Value *pointerValue : pointToSet[pointer]){
       pointToSet[pointerValue].insert(value);
     }
   }

   void computeLoadInst(LoadInst* loadInst, LivenessInfo* dfval) {
       Value *pointer = loadInst->getPointerOperand();
     /*if (GetElementPtrInst *getElementPtrInst = dyn_cast<GetElementPtrInst>(pointer)){
       errs() << ">>>>> load\n";
       pointer->dump();
       PointToSetType &pointToSet = dfval->PointToSet;
       pointToSet[loadInst] = {};
       ValueSetType &valueSet = pointToSet[loadInst];
       for (Value *pointerValue : pointToSet[pointer]) {
         errs() << pointerValue << " " << pointToSet[pointerValue].size();
         pointerValue->dump();
         valueSet.insert(pointToSet[pointerValue].begin(), pointToSet[pointerValue].end());
       }
       errs() << ">>>>>\n";
     }*/
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
           handleFunctionArgs(callInst, func, dfval);

       } else {
           #ifdef DEBUG
           errs() << "value is a function pointer" << "\n";
           value->dump();
           #endif
           if (dfval->PointToSet.count(value) != 0) {
               std::set<Function* > funcSet = {};
               ValueSetType PointSet = dfval->PointToSet[value];
               for(ValueSetType::iterator iter = PointSet.begin(); iter != PointSet.end(); ++iter) {
                   if (Function* funcTemp = dyn_cast<Function>(*iter)) {
                       functionWorkList.insert(funcTemp);
                       funcSet.insert(funcTemp);
                       handleFunctionArgs(callInst, funcTemp, dfval);
                   }
               }
               finalResult.insert(std::make_pair(callInst, funcSet));
           }
       }
       return;
   } 
   void computeReturnInst(ReturnInst* returnInst, LivenessInfo* dfval) {
       return;
   }

   void computeAllocaInst(AllocaInst *allocaInst, LivenessInfo *dfval) {
     PointToSetType &pointToSet = dfval->PointToSet;
     pointToSet[allocaInst] = {};
   }

   void computeGetElementPtrInst(GetElementPtrInst* getElementPtrInst, LivenessInfo* dfval) {
/*      errs() << ">>>>> " << getElementPtrInst->getNumIndices() << " " << getElementPtrInst->getPointerAddressSpace() << " " << getElementPtrInst->getAddressSpace()  << '\n';
      getElementPtrInst->dump();
      getElementPtrInst->getPointerOperand()->dump();
      errs() << "<<<<<\n";*/
     PointToSetType &pointToSet = dfval->PointToSet;
     pointToSet[getElementPtrInst] = {getElementPtrInst->getPointerOperand()};
   }
   void compDFVal(Instruction *inst, LivenessInfo * dfval) override{
        if (isa<DbgInfoIntrinsic>(inst)) return;
        inst->dump();
        if (PHINode* phiNode = dyn_cast<PHINode>(inst)) {
            #ifdef DEBUG
                errs() << phiNode->getName() << "\n";
            #endif
            computePhiNode(phiNode, dfval);
        } else if (StoreInst* storeInst = dyn_cast<StoreInst>(inst)) {
            storeInst->dump();
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



