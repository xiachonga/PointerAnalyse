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

#include <llvm/Support/CommandLine.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Support/ToolOutputFile.h>

#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>


#include <llvm/Transforms/Utils.h>
#include <llvm/Transforms/Scalar.h>

#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>

#include "Liveness.h"
#include "Dataflow.h"

#define DEBUG
using namespace llvm;
static ManagedStatic<LLVMContext> GlobalContext;
static LLVMContext &getGlobalContext() { return *GlobalContext; }

struct EnableFunctionOptPass : public FunctionPass {
    static char ID;
    EnableFunctionOptPass() :FunctionPass(ID) {}
    bool runOnFunction(Function & F) override {
        if (F.hasFnAttribute(Attribute::OptimizeNone))
        {
            F.removeFnAttr(Attribute::OptimizeNone);
        }
        return true;
    }
};

char EnableFunctionOptPass::ID = 0;

///!TODO TO BE COMPLETED BY YOU FOR ASSIGNMENT 3
struct FuncPtrPass : public ModulePass {
    static char ID; // Pass identification, replacement for typeid
    FuncPtrPass() : ModulePass(ID) {}
    std::set<Function* > functionWorkList;

    bool runOnModule(Module &M) override {
       for (Module::iterator fn = M.begin(); fn != M.end(); ++fn) {
           if ((&*fn)->isIntrinsic()) {
                continue;
           }
           functionWorkList.insert(&*fn);
       }
       LivenessVisitor visitor;
       DataflowResult<LivenessInfo>::Type result;
       LivenessInfo initval;
       while (!functionWorkList.empty()) {
            Function* F = *(functionWorkList.begin());
            functionWorkList.erase(F);
            std::map<Function*, LivenessInfo> funcArgPointSet = visitor.getFunctionArgPointSet();
            if (funcArgPointSet.count(F)) {
                initval = funcArgPointSet[F];
            }
            compForwardDataflow(F, &visitor, &result, initval); // initval是否还需要根据需要修改？
            functionWorkList.insert(visitor.getFunctionWorkList().begin(), visitor.getFunctionWorkList().end());
            std::set<Function* > funcSet = {};
            visitor.setFunctionWorkList(funcSet);
       } 
       // TODO print result
       PrintResult(visitor.getFinalResult());
       return false; 
    }
    
    void PrintResult(std::map<CallInst*, std::set<Function*> > Result) {
        unsigned int line = 0;
		int flag = 0;
		int flag2 = 0;
		for (std::pair<CallInst *, std::set<Function *> > CIMF : Result)
		{
			unsigned int newLine = CIMF.first->getDebugLoc().getLine();
			if (flag != 0 && newLine != line)
			{
				errs() << '\n';
				flag2 = 0;
			}
			flag = 1;
			if (newLine != line)
			{
				errs() << newLine << " :";
				line = newLine;
			}
			for (Function *F : CIMF.second)
			{
				if (flag2 == 0) {
					errs() << ' ' << F->getName();
					flag2 = 1;
				} else {
					errs() << ", " << F->getName();
				}
				
			}
		}
		errs() << '\n';
    }
};


char FuncPtrPass::ID = 0;
static RegisterPass<FuncPtrPass> X("funcptrpass", "Print function call instruction");

char Liveness::ID = 0;
static RegisterPass<Liveness> Y("liveness", "Liveness Dataflow Analysis");

static cl::opt<std::string>
InputFilename(cl::Positional,
              cl::desc("<filename>.bc"),
              cl::init(""));


int main(int argc, char **argv) {
   LLVMContext &Context = getGlobalContext();
   SMDiagnostic Err;
   // Parse the command line to read the Inputfilename
   cl::ParseCommandLineOptions(argc, argv,
                              "FuncPtrPass \n My first LLVM too which does not do much.\n");


   // Load the input module
   std::unique_ptr<Module> M = parseIRFile(InputFilename, Err, Context);
   if (!M) {
      Err.print(argv[0], errs());
      return 1;
   }

   llvm::legacy::PassManager Passes;
//#if LLVM_VERSION_MAJOR == 5
   Passes.add(new EnableFunctionOptPass());
//#endif
   ///Transform it to SSA
   Passes.add(llvm::createPromoteMemoryToRegisterPass());

   /// Your pass to print Function and Call Instructions
   //Passes.add(new Liveness());
   Passes.add(new FuncPtrPass());
   Passes.run(*M.get());
#ifndef NDEBUG
   //system("pause");
#endif
}

