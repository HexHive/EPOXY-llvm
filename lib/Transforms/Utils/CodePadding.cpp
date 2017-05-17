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

#define DEBUG_TYPE "code-padding"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/RandomNumberGenerator.h"


using namespace llvm;

static cl::opt<unsigned> FunctionPaddingBytes("randomize-function-list",
                                  cl::desc("Number of bytes to use for function padding"),
                                  cl::init(0));


STATISTIC(NumPads     , "Number of function pads");
namespace {
  // Hello - The first implementation, without getAnalysisUsage.
  struct CodePadding : public ModulePass{
    // Pass identification, replacement for typeid
    //static char ID;
    CodePadding(int paddingSize=0) : ModulePass(ID) {
      	PaddingSize=FunctionPaddingBytes;
    }

    virtual bool runOnModule(Module &M) {
      Function * default_handler;
      BasicBlock * halt_bb;
      BasicBlock * end_bb;
      IRBuilder<> *IRB;
      NumPads = 0;
      if(FunctionPaddingBytes == 0){
        return true;
      }

      FunctionType *FT = FunctionType::get(Type::getVoidTy(M.getContext()),false);
      //errs() << "Running Code Padding Pass" <<"\n";
      IRB =new IRBuilder<>(getGlobalContext());
      if (PaddingSize >0){
    	  DEBUG(errs() << "Adding Padding" <<"\n");
    	  if (M.getFunction("__default_invalid_addr_handler")==NULL){
    		  DEBUG(errs() << "Adding Default Handler" <<"\n");
    		  default_handler=Function::Create(FT,Function::ExternalLinkage,"__default_invalid_addr_handler",&M);
    		  default_handler->addFnAttr(Attribute::AttrKind::NoUnwind);
          default_handler->addFnAttr(Attribute::AttrKind::Naked);
          default_handler->addFnAttr(Attribute::AttrKind::OptimizeNone);
          default_handler->addFnAttr(Attribute::AttrKind::NoInline);
          //default_handler->addFnAttr(Attribute::AttrKind::Used);
          default_handler->setDoesNotReturn();
    		  //default_handler->setAttributes(AttributeSet )(); Set naked attribute
    		  DEBUG(errs() << "Added Handler" <<"\n");
    		  halt_bb=BasicBlock::Create(getGlobalContext(), "entry", default_handler);
              end_bb=BasicBlock::Create(getGlobalContext(), "loop", default_handler);
    		  //default_handler->
          DEBUG(errs() << "Got Here" <<"\n");
    		  IRB->SetInsertPoint(halt_bb);
    		  IRB->CreateBr(end_bb);
              //IRB->CreateUnreachable();
          DEBUG(errs() << "Got Here" <<"\n");
              IRB->SetInsertPoint(end_bb);
            IRB->CreateBr(end_bb);

    		  DEBUG(default_handler->dump());
    		  verifyFunction(*default_handler);
    		  DEBUG(errs() << "Done Adding Default Handler" <<"\n");
    	  }else{
    		  default_handler=cast<Function>(M.getFunction("__default_invalid_addr_handler"));
    		  halt_bb=&cast<BasicBlock>(default_handler->getEntryBlock());
    	  }
        //on cortex m4 Pad function is 4 bytes
          for(int i=0;i<(PaddingSize/4);i++){
    		  DEBUG(errs() << "Adding Function:" << i<<"\n");
          NumPads++;
    		  Function *pad_funct;
              //BasicBlock *endBB;
    		  BasicBlock *entryBB;

    		  pad_funct=Function::Create(FT,Function::InternalLinkage,"__pad",&M);
    		  pad_funct->addFnAttr(Attribute::AttrKind::NoUnwind);
          pad_funct->addFnAttr(Attribute::AttrKind::Naked);
          pad_funct->addFnAttr(Attribute::AttrKind::OptimizeNone);
          pad_funct->addFnAttr(Attribute::AttrKind::NoInline);
          //default_handler->addFnAttr(Attribute::AttrKind::Used);
    		  pad_funct->setDoesNotReturn();
    		  //set naked attribute
    		  entryBB = BasicBlock::Create(M.getContext(), "entry", pad_funct);//need so entry block doesn't have any predecessors
              //endBB = BasicBlock::Create(M.getContext(), "end", pad_funct);
     		  IRB->SetInsertPoint(entryBB);
              //IRB->CreateBr(endBB);
              IRB->CreateCall(default_handler);
              IRB->CreateUnreachable();
              //IRB->SetInsertPoint(endBB);
  			  //Create branch back to itself, makes a system halt;

  			  //IRB->CreateBr(endBB); (Insert two byte nop)
              //IRB->CreateBr(endBB);
          DEBUG(pad_funct->dump());
    	  }
    	  DEBUG(dbgs() << "[Code Padding] All Done:" <<"\n");
        DEBUG(errs() << "Deleting IRB" <<"\n");
    	  delete IRB;
        DEBUG(errs() << "Return True" <<"\n");
        RandomNumberGenerator *Gen= M.createRNG(this);
        //Gen->shuffle<Function>(M.getFunctionList());
        shuffle_functions(M);
        //std::shuffle<>(M.FunctionList.begin(),M.FunctionList.end(),std::rand);
        //M.createRNG(this)->shuffle<FunctionType>(M.getFunctionList());
    	  return true;
      }
      DEBUG(errs() << "Deleting IRB" <<"\n");
      delete IRB;
      DEBUG(errs() << "Got False" <<"\n");
      return false;
    }

    void shuffle_functions (Module & M){
      RandomNumberGenerator *Gen= M.createRNG(this);

      SmallVector<Function *, 10> sv;
      DEBUG(dbgs()<<"Normal Order\n" << "\n");
      for (iplist<Function>::iterator itr=M.getFunctionList().begin();
                itr!=M.getFunctionList().end();){
        Function * F = M.getFunctionList().remove(itr);
        DEBUG(dbgs()<<F->getName() << "\n");
        sv.push_back(F);
        //M.getFunctionList().remove(&F);

      }

      DEBUG(dbgs()<<"Shuffled Functions\n" << "\n");
      for (size_t i=sv.size()-1;i>0;i--){
        size_t j=((*Gen)())%i;
        std::swap(sv[i],sv[j]);

      }

      for (Function *F :sv){
        M.getFunctionList().push_back(F);
        DEBUG(dbgs()<<F->getName() << "\n");
      }
    }

    virtual const char *getPassName() const{
    	return "CodePaddingPass";
    }
    static char ID;

  void getAnalysisUsage(AnalysisUsage &Info) const{
    //Info.addRequired<GlobalOpt>();
    //Info.addRequired<GlobalDCE>();
    Info.setPreservesAll();

  }

  private:

    int num_functs_added = 0;
    int PaddingSize;
  };
}// end anonymous namespace


char CodePadding::ID = 0;

INITIALIZE_PASS_BEGIN(CodePadding, "code-padding", "Code padding pass",false, false)
INITIALIZE_PASS_END(CodePadding, "code-padding", "Code padding pass",false, false)

ModulePass *llvm::createCodePaddingPass(unsigned num_bytes){
  DEBUG(errs() << "Creating Code Padding Pass" <<"\n");
  return new CodePadding(num_bytes);
}
