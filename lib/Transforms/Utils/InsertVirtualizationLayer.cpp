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


#include "llvm/Transforms/Instrumentation.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/DiagnosticInfo.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/ADT/Statistic.h"

#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/TargetLibraryInfo.h"


#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <algorithm>
#include <set>
#include <map>

using namespace llvm;

#define DEBUG_TYPE "virtualization-layer"
#define NUM_REGIONS 8


STATISTIC(AddrElevated, "Number of addresses elevated");
STATISTIC(NumConstAddrs, "Number of Constant Addresses Detected");
STATISTIC(InstElevated, "Number of Instructions Elevated");
namespace {

  typedef struct{
  long Addr;
  long long Size;
  int Permissions;
  int Execute;
  int Region;
  bool C;
  bool B;
  bool S;
  bool Valid;
  bool isPtr;
  std::string Ptr;

}RegionsStruct;


static cl::opt<std::string>
MPURegionsFile("reduce-privileges",
         cl::desc("MPU regions configuration"), cl::init("-"),cl::value_desc("filename"));

static cl::opt<bool>
AddEdivertLayer("add-edivirt",
         cl::desc("Add Edivirt MPU Managment Layer"), cl::init(false));


  struct InsertVirtualizationLayer : public ModulePass {
    static char ID; // Pass identification, replacement for typeid
    //AliasAnalysis *AA;
    //MemoryDependenceResults *MD;
    Module * Mod;


    //InsertVirtualizationLayer() : FunctionPass(ID),  AA(nullptr), MD(nullptr){}
    InsertVirtualizationLayer() : ModulePass(ID){}
    RegionsStruct regions[NUM_REGIONS];
    const TargetLibraryInfo *TLI;

    const char *getPassName() const override{
      return "InsertVirtualizationLayer";
    }

    uint32_t get_RASR(RegionsStruct & region){
      /*
        Calculates the needed value for the RASR register for the ARMV7-M MPU's RASR Register
        This controlls the permissions and size
      */
      uint32_t rasr = 0;
      if (region.Valid){

        if (!region.Execute){
          rasr |=(1<<28);
        }

        rasr |=(region.Permissions<<24);
         if (region.S)
          rasr |=1<<18;
        if (region.C)
          rasr |=1<<17;
        if (region.B)
          rasr |=1<<16;

        //bit 15:8 subregions not using
        //bits 7:6 not used
        //bit 5:1 size
        rasr |=((region.Size&0x1F)<<1);
        rasr |=1; //Set enable
      }
      else{
        rasr = 0;
      }
      return rasr;
    }

    void add_mpu_configs(Module & M, IRBuilder<> *IRB){
    /*
      Setup the MPU for the ARMV7-M MPU   (Cortex M 3,4, and 7)
    */

      //Constant * MPU_Region_Number;
      Constant * MPU_RBAR;
      Constant * MPU_RASR;
      Value *R;

      MPU_RBAR = ConstantInt::get(Type::getInt32Ty(M.getContext()),0xE000ED9C);
      MPU_RBAR = ConstantExpr::getIntToPtr(MPU_RBAR,Type::getInt32PtrTy(M.getContext()));
      DEBUG(dbgs()<<"Created MPU_RBAR\n");

      MPU_RASR = ConstantInt::get(Type::getInt32Ty(M.getContext()),0xE000EDA0);
      MPU_RASR = ConstantExpr::getIntToPtr(MPU_RASR,Type::getInt32PtrTy(M.getContext()));
      DEBUG(dbgs()<<"Created MPU_RASR\n");


      for(uint32_t i=0;i<NUM_REGIONS;i++){
        uint32_t Addr;
        uint32_t rasr;
        if (regions[i].Valid){
          if (regions[i].isPtr){

            DEBUG(dbgs()<<"Set to MPU to address of variable" <<regions[i].Ptr <<"\n");
            Value * Address = M.getOrInsertGlobal(regions[i].Ptr,Type::getInt32PtrTy(M.getContext()));

            DEBUG(Address->dump());
            R = IRB->CreatePtrToInt(Address,Type::getInt32Ty(M.getContext()));
            DEBUG(R->dump());
            R = IRB->CreateAnd(R,0xFFFFFFE0);
            //DEBUG(R->dump());
            DEBUG(dbgs()<<"Got to here\n");
            R = IRB->CreateOr(R,(0x10|(i &0xF)));
            IRB->CreateStore(R,MPU_RBAR,true);
            DEBUG(dbgs()<<"Set to MPU to address of variable" <<regions[i].Ptr <<"\n");

          }else{
             Addr = (uint32_t)(regions[i].Addr &0xFFFFFFE0)|0x10|(i &0xF); //Sets Address and region number
             IRB->CreateStore(ConstantInt::get(Type::getInt32Ty(M.getContext()),Addr),MPU_RBAR,true);
          }
          rasr=get_RASR(regions[i]);
          IRB->CreateStore(ConstantInt::get(Type::getInt32Ty(M.getContext()),rasr),MPU_RASR,true);
          DEBUG(dbgs()<<"Wrote MPU Config for regions "<< i <<" RBAR:0x");
          DEBUG(dbgs().write_hex(Addr); dbgs()<<" RASR:0x"; dbgs().write_hex(rasr);dbgs()<<"\n");
        }
      }

    }

    void print_region(RegionsStruct &region){
    /*
      Prints the regions struct used for debugging

    */
      if (region.Valid){
         DEBUG(dbgs() <<"Region: " <<region.Region <<"\n");
        if (region.isPtr){
           DEBUG(dbgs() <<"Ptr: " <<region.Ptr <<"\n") ;
        }else{
           DEBUG(dbgs() <<"Addr: " <<region.Addr <<"\n");
        }
         DEBUG(dbgs() <<"Size: " <<region.Size <<"\n");
         DEBUG(dbgs() <<"Permissions: " <<region.Permissions <<"\n");
         DEBUG(dbgs() <<"C: " <<region.C <<"\n");
         DEBUG(dbgs() <<"B: " <<region.B <<"\n");
         DEBUG(dbgs() <<"S: " <<region.S <<"\n");
         DEBUG(dbgs() <<"isPtr: " <<region.isPtr <<"\n");
      }
    }

    bool parse_file(){
      /*
        Parser the permissions input file it should be of the format
        Region :Permissions   :Start       :Size :CBS
        0      :P-RW,U-RW,XN  :0x00000000  :4GB  :101
        4      :P-,U-,XN      :&__unsafestack_guard_start :32B  :101
        5      :P-RW,U-R,XN   :0xE000E000  :4KB  :101
        6      :P-RW,U-R,XN   :0x40013800  :512B  :101
        7      :P-R,U-R,X     :0x00000000  :256MB  :101
      */
      std::ifstream permissions_file(MPURegionsFile);
      std::string line;
      //permissions_file.open('permissions_file.txt');

      for (int i=0; i<NUM_REGIONS ; i++){
        regions[i].Valid = false;
      }
      if(!permissions_file.fail()){
        getline(permissions_file,line);  //read and discard header
        int r_num;
        while (getline(permissions_file,line)){
          DEBUG(dbgs() << "Parsing:" <<line <<"\n");
          //Region :Permissions   :Start       :Size :CBS
          std::stringstream ss(line);
          std::string field;
          //Region
          getline(ss,field,':');
          r_num = stoi(field);
          DEBUG(dbgs()<< "Region: "<<"\n");
          if (r_num >=0 && r_num < NUM_REGIONS){
            regions[r_num].Region=r_num;
            regions[r_num].Valid=false;
          }else{

            //errs() << "Skipping Invalid Region: " <<field <<"\n";
            break;
          }

         DEBUG(dbgs() << "Permissions: "<<"\n");
          //permissions
          getline(ss,field,':');
          field.erase(remove_if(field.begin(), field.end(), ::isspace), field.end());
          if(field.compare("P-,U-,XN") == 0){
            regions[r_num].Permissions = 000;
            regions[r_num].Execute =false;
          }else if (field.compare("P-,U-,X") == 0){
            regions[r_num].Permissions = 000;
            regions[r_num].Execute =true;

          }else if (field.compare("P-RW,U-,XN") == 0){
            regions[r_num].Permissions = 001;
            regions[r_num].Execute =false;
          }else if (field.compare("P-RW,U-,X") == 0){
            regions[r_num].Permissions = 1;
            regions[r_num].Execute =true;

          }else if (field.compare("P-RW,U-R,XN") == 0){
            regions[r_num].Permissions = 2;
            regions[r_num].Execute =false;
          }else if (field.compare("P-RW,U-R,X") == 0){
            regions[r_num].Permissions = 2;
            regions[r_num].Execute =true;

          }else if (field.compare("P-RW,U-RW,XN") == 0){
            regions[r_num].Permissions = 3;
            regions[r_num].Execute = false;
          }else if (field.compare("P-RW,U-RW,X") == 0){
            regions[r_num].Permissions = 3;
            regions[r_num].Execute = true;

          }else if (field.compare("P-R,U-,XN") == 0){
            regions[r_num].Execute = false;
            regions[r_num].Permissions = 5;
          }else if (field.compare("P-R,U-,X") == 0){
            regions[r_num].Execute = true;
            regions[r_num].Permissions = 5;

          }else if (field.compare("P-R,U-R,XN") == 0){
            regions[r_num].Execute = false;
            regions[r_num].Permissions = 7;
          }else if (field.compare("P-R,U-R,X") == 0){
            regions[r_num].Execute = true;
            regions[r_num].Permissions = 7;
          }else{
           //errs() <<"Invalid Permissions:"<<field <<"\n";
            Mod->getContext().emitError("Invalid Permissions in Permissions file");
            break;
          }
          //Start
         DEBUG(dbgs() << "Start"<<"\n");
          getline(ss,field,':');
          if(field[0]=='&'){
            regions[r_num].isPtr=true;
            regions[r_num].Ptr = field = field.substr(1);
            field.erase(remove(field.begin(),field.end(),' '));
            regions[r_num].Ptr = field;
          }else{
            regions[r_num].isPtr=false;
            regions[r_num].Addr=stol(field,nullptr,16);
          }
          //Size
              //Size
           DEBUG(dbgs() << "Size: "<<"\n");
          long size;
          getline(ss,field,':');
          field.erase(remove_if(field.begin(), field.end(), ::isspace), field.end());
           DEBUG(dbgs() << "Field:"<<field <<"\n");
          if (field.compare("32B")==0){
            size=4;
          }else if (field.compare("64B")==0){
            size=5;
          }else if (field.compare("128B")==0){
            size=6;
          }else if (field.compare("256B")==0){
            size=7;
          }else if (field.compare("512B")==0){
            size=8;
          }else if (field.compare("1KB")==0){
            size=9;
          }else if (field.compare("2KB")==0){
            size=10;
          }else if (field.compare("4KB")==0){
            size=11;
          }else if (field.compare("8KB")==0){
            size=12;
          }else if (field.compare("16KB")==0){
            size=13;
          }else if (field.compare("32KB")==0){
            size=14;
          }else if (field.compare("64KB")==0){
            size=15;
          }else if (field.compare("128KB")==0){
            size=16;
          }else if (field.compare("256KB")==0){
            size=17;
          }else if (field.compare("512KB")==0){
            size=18;
          }else if (field.compare("1MB")==0){
            size=19;
          }else if (field.compare("2MB")==0){
            size=20;
          }else if (field.compare("4MB")==0){
            size=21;
          }else if (field.compare("8MB")==0){
            size=22;
          }else if (field.compare("16MB")==0){
            size=23;
          }else if (field.compare("32MB")==0){
            size=24;
          }else if (field.compare("64MB")==0){
            size=25;
          }else if (field.compare("128MB")==0){
            size=26;
          }else if (field.compare("256MB")==0){
            size=27;
          }else if (field.compare("512MB")==0){
            size=28;
          }else if (field.compare("1GB")==0){
            size=29;
          }else if (field.compare("2GB")==0){
            size=30;
          }else if (field.compare("4GB")==0){
            size=31;
          }else{
             DEBUG(dbgs() <<"Invalid Size:"<<field <<"\n");
            break;
          }
          regions[r_num].Size=size;


          //Cache (CBS)
          DEBUG(dbgs() << "CBS" <<"\n");
          getline(ss,field);
          if (field.size() >=3){
            regions[r_num].C = field[0]=='1' ? true: false;
            regions[r_num].B = field[1]=='1' ? true: false;
            regions[r_num].S = field[2]=='1' ? true: false;
            regions[r_num].Valid = true;
          }

        }

      }else{
        errs() << "Cannot Open file:"<<MPURegionsFile <<"\n";
        return false;

      }
      return true;
    }

    bool doInitialization(Module &M) override{
        Mod = &M;
        if (!AddEdivertLayer){
            return false;
        }

        build_mpu_config(M);
        //http://homes.cs.washington.edu/~bholt/posts/llvm-quick-tricks.html
        //Method for parsing annotations
        //Get annotations
        auto global_annos = M.getNamedGlobal("llvm.global.annotations");
        if (global_annos) {
          auto a = cast<ConstantArray>(global_annos->getOperand(0));
          errs() <<"Annotations\n";
          a->dump();
          for (unsigned int i=0; i < a->getNumOperands(); i++) {
            auto e = cast<ConstantStruct>(a->getOperand(i));
            //if function and intercept then we insert a shim function that gets
            //called when ever the intercept function gets call this diverts execution
            //the the function with the annotation.
            if (Function * fn = dyn_cast<Function>(e->getOperand(0)->getOperand(0))) {
              StringRef anno = cast<ConstantDataArray>(cast<GlobalVariable>(e->getOperand(1)->getOperand(0))->getOperand(0))->getAsCString();
              errs() << anno <<"\n";
              fn->addFnAttr(anno); // <-- add function annotation here
              if (anno.startswith("intercept:")){
                  std::pair<StringRef,StringRef> p = anno.split(":");
                  Function * intercept_Funct = M.getFunction(p.second);
                  IRBuilder <> *IRB;
                  IRB = new IRBuilder<>(M.getContext());
                  InlineAsm * RegCall = nullptr;
                  if(intercept_Funct){
                    //Change function name and branch to it
                    const std::string new_name = "__intercepted_edivirt_" + intercept_Funct->getName().str();
                    intercept_Funct->setName(new_name);
                    //Change function name and b ranch to it
                    const std::string inst_str2 = "b " + new_name;
                    InlineAsm * RegCall = InlineAsm::get(FunctionType::get(Type::getVoidTy(M.getContext()),false),
                                                    inst_str2,"",false);
                  }

                  const std::string inst_str = "push {r0,r1,r2,r3,lr} \n\t MRS r0, msp\n\t bl " + fn->getName().str() + "\n\t pop {r0,r1,r2,r3,lr}";
                  InlineAsm * ShimAsmCall = InlineAsm::get(
                                FunctionType::get(Type::getVoidTy(M.getContext()),false),
                                                  inst_str,"",false);
                  FunctionType *FT = FunctionType::get(Type::getVoidTy(M.getContext()),false);
                  Function * ShimFunct = Function::Create(FT,Function::ExternalLinkage,p.second,&M);
                  ShimFunct->addFnAttr(Attribute::AttrKind::Naked);
                  ShimFunct->setDoesNotReturn();
                  BasicBlock *EntryBB = BasicBlock::Create(getGlobalContext(), "entry", ShimFunct);
                  IRB->SetInsertPoint(EntryBB);
                  IRB->CreateCall(ShimAsmCall);
                  if(RegCall){
                    IRB->CreateCall(RegCall);
                  }
                  IRB->CreateUnreachable();
                  delete IRB;
              }
            }
          }
        }

        Function * SysInt = M.getFunction("SystemInit");
        if(SysInt){
            SysInt->addFnAttr("no-virt");
        }
        return false;

    }


    bool isConstAddr(Instruction * inst){
      Value * operand = nullptr;
      bool usesConstAddress = false;
      if(isa<LoadInst>(inst)){
        operand = inst->getOperand(0);
      }else if (isa<StoreInst>(inst)){
        operand = inst->getOperand(1);
      }else{
        return false;
      }

      if (operand){
        // captures direct use of inttoptr  e.g inttoptr (i32 40020000 to i32*)
        if (ConstantExpr * intPtr = dyn_cast<ConstantExpr>(operand)){
            Instruction * inst = intPtr->getAsInstruction();
          if (CastInst * castPtr = dyn_cast<CastInst>(inst)){
            if (castPtr->getDestTy()->isPointerTy()){  //know it is a constant cast to a pointer
              castPtr->getOperand(0);
              if(ConstantInt *constInt = dyn_cast<ConstantInt>(castPtr->getOperand(0))){
                errs() << "Address is:" <<constInt->getValue() <<"\n";
              }
              usesConstAddress = true;
            }
          }
        }
        }/*else if(){

        }*/

      return usesConstAddress;
    }


    APInt getAddr(Value * c ,const DataLayout & DL){
      Type *IntPtrTy = DL.getIntPtrType(Mod->getContext())->getScalarType();
      APInt addr  = APInt::getNullValue(IntPtrTy->getIntegerBitWidth());
      if (GEPOperator * GEPConst = dyn_cast<GEPOperator>(c)){
        APInt Offset = APInt::getNullValue(IntPtrTy->getIntegerBitWidth());
        addr = getAddr(GEPConst->getPointerOperand(),DL);
        if (GEPConst->accumulateConstantOffset(DL,Offset)){
          addr +=Offset;
        }else{
          Offset = 0;
        }
      }
      else if (ConstantExpr * ConstExpr = dyn_cast<ConstantExpr>(c)){
          Instruction * I = ConstExpr->getAsInstruction();  //this is causing problems.
          //errs() << "Value: " << ConstExpr->getValue();
          if(IntToPtrInst * ptrInst = dyn_cast<IntToPtrInst>(I)){
             if(ConstantInt * CInt =dyn_cast<ConstantInt>(ptrInst->getOperand(0))){
               addr = CInt->getValue();
              }
          }else{
            //assert(0 && "Unhandled Pointer Type Unknown Addr");
          }
          delete I;
      }else if (GlobalVariable *GV = dyn_cast<GlobalVariable>(c)){
          errs()<< "Getting Addr of GV\n";
          GV->dump();
            if (GV->getType()->isPointerTy() && GV->hasInitializer()){
                Constant *C = GV->getInitializer();

                errs()<<"Initializer \n";
                C->dump();
                if(ConstantInt * CInt =dyn_cast<ConstantInt>(C)){
                    addr = CInt->getValue();
                }else{
                    //addr = getAddr(C,DL);
                }
            }
      }
      else if(ConstantInt * CInt =dyn_cast<ConstantInt>(c)){
          addr = CInt->getValue();
      }
      else {
        assert( 0  && "Value must be a GEP or ConstExpr");
      }
      return addr;
    }

    Constant * checkConstAddr(Value * Ptr,std::map<Value *,Constant *> &Memory, int tab_level){
      for(int i=0; i<tab_level+1; i++){
        errs()<<"    ";
      }
      errs()<<tab_level<<": ";
      Ptr->dump();
      //Constant * retValue = nullptr;

      if (Constant * C = dyn_cast_or_null<Constant>(Ptr)){
        return C;
      }

      auto it = Memory.find(Ptr);
      if( it != Memory.end()){
        return it->second;
      }
      else if(StoreInst *SI = dyn_cast<StoreInst>(Ptr)){
        return checkConstAddr(SI->getPointerOperand(),Memory,tab_level+1);
      }
      else if(LoadInst * LI = dyn_cast<LoadInst>(Ptr)){
        return checkConstAddr(LI->getPointerOperand(),Memory,tab_level+1);
      }
      return nullptr;
    }


    Constant * getAddressForPtr(Value * Ptr,std::map<Value *,Constant *> &Memory,int tab_level){
        /* For a pointer determines its constant value, returns nullptr otherwise
         * This is just an alias for getValue for ease of understanding
         * Ptr:  Pointer to get Address For
         * Memory: Memory mapping pointers to values
         */
        return getValue(Ptr,Memory,tab_level);

    }

    Constant * getAddressAccessed(Value * Inst,std::map<Value *,Constant *> &Memory){
        /*  Returns the address that is accessed if it is constant nullptr otherwise
         *  Inst: Instruction to deteremine address for
         *  Memory: A map of values for memory locations used to track
         *  propigation of constants
         */
        if(StoreInst *SI = dyn_cast<StoreInst>(Inst)){
            Constant * ptrValue = nullptr;
            Value * PtrOp = SI->getPointerOperand();
            Constant * value = getValue(SI->getOperand(0),Memory,1);

            ptrValue = getAddressForPtr(PtrOp,Memory,1);
            Memory[PtrOp] = value;
            return ptrValue;
        }
        else if(LoadInst * LI = dyn_cast<LoadInst>(Inst)){
            Value * PtrOp = LI->getPointerOperand();
            Memory[LI] = getValueAtAddr(PtrOp,Memory,1);
            return getAddressForPtr(PtrOp,Memory,1);
        }

        return nullptr;
    }

    Constant * getGVValue(GlobalVariable * GV,std::map<Value *,Constant *> &Memory, int tab_level ){
        return nullptr;
    }

    Constant * getValue(Value * Val,std::map<Value *,Constant *> &Memory, int tab_level){
        /* Tries to find a constant int that represents the value,
         * Returns it if it does
         */
        if(GEPOperator * GEPOp = dyn_cast<GEPOperator>(Val)){
            Constant * ConstPtr = getValue(GEPOp->getPointerOperand(),Memory,tab_level+1);
            const DataLayout DL = Mod->getDataLayout();
            //Constant * Offset = getValue(GEPOp->getOperand(1),Memory,tab_level+1);
            if (ConstantInt *IntVal = dyn_cast_or_null<ConstantInt>(ConstPtr)){
                APInt Offset = APInt::getNullValue(APInt::getNullValue(DL.getPointerSizeInBits()).getBitWidth());
                if (GEPOp->accumulateConstantOffset(Mod->getDataLayout(),Offset)){
                    return Constant::getIntegerValue(Type::getInt32Ty(Mod->getContext()),Offset+IntVal->getUniqueInteger());
                }
            }
        }
        else if(GlobalVariable *GV = dyn_cast<GlobalVariable>(Val)){
            return getGVValue(GV,Memory,tab_level);
        }
        else if(LoadInst * LI = dyn_cast<LoadInst>(Val)){
            return getValueAtAddr(LI->getPointerOperand(),Memory,tab_level+1);
        }
        else if (IntToPtrInst * IntPtr = dyn_cast<IntToPtrInst>(Val)){
            //errs() << "Got IntToPtr\n";
            return getValue(IntPtr->getOperand(0),Memory,tab_level+1);
        }else if (CastInst * Cast = dyn_cast<CastInst>(Val)){
            //errs() << "Got Cast\n";
            Cast->stripPointerCasts()->dump();
        }
        else if (ConstantExpr * C = dyn_cast<ConstantExpr>(Val)){
            //errs() << "Got ConstantExpr\n";
            Instruction * Inst = C->getAsInstruction();
            Constant * Cons = getValue(Inst,Memory,tab_level);
            delete Inst;
            return Cons;
        }
        else if (ConstantInt * C = dyn_cast<ConstantInt>(Val)){
            return C;
        }
        return nullptr;
    }

    Constant * getValueAtAddr(Value * Addr,std::map<Value *,Constant *> &Memory, int tab_level){
    /*  Returns the value at the input address, returns nullptr if not constant
     *  Value: Addr for which to determine constant value
     *  Memory: Memory mapping addresses to constant values
     *  tab_level: used to print searches
    */
      Constant * retValue = nullptr;

      //If there is a value for this location return it
      std::map<Value *,Constant *> ::iterator it = Memory.find(Addr);
      if(it != Memory.end()){
        //If there is a value for this location.end()){
            retValue = it->second;
      }
      else if (GlobalVariable *GV = dyn_cast<GlobalVariable>(Addr)){  //realy need to check if is a pointer with constant value
          if (GV->getType()->isPtrOrPtrVectorTy() && GV->hasInitializer()){
              Constant *C = GV->getInitializer();
              if(!C->isZeroValue()){
                Memory[GV] = C;
                retValue = C;
              }
          }
      }
      else if (AllocaInst * AI = dyn_cast<AllocaInst>(Addr)){
          //Mod->getContext().emitError("Accessed Alloc before it was placed in memory");
      }
      return retValue;
    }


    APInt getAddrForDeref(Value * Inst,std::map<Value *,APInt> &ValueCache, const DataLayout & DL, int tab_level){
          //Builds a memory of all addresses accessed, this is then checked later
          //to identify constants that are dereferenced
          //Type *IntPtrTy = DL.getIntPtrType(Type::getInt32PtrTy(Mod->getContext()));
          APInt retValue = APInt::getNullValue(DL.getPointerSizeInBits());
          std::map<Value *,APInt> ::iterator it = ValueCache.find(Inst);
          if(it != ValueCache.end()){
                retValue = it->second;
          }
          else if (Constant * C = dyn_cast<Constant>(Inst)){
              retValue = getAddr(C,DL);
          }
          else if(StoreInst *SI = dyn_cast<StoreInst>(Inst)){
            retValue = getAddrForDeref(SI->getPointerOperand(),ValueCache,DL, tab_level+1);
            APInt newAddr = getAddrForDeref(SI->getOperand(0),ValueCache,DL, tab_level+1);
            ValueCache[SI->getPointerOperand()] = newAddr;
          }
          else if(LoadInst * LI = dyn_cast<LoadInst>(Inst)){
            //ValueCache[LI]=getAddrForDeref()
            // If this is a load instruction form an alloca, we are loading from a local
            // which means that this instuction now has the value of that was stored for
            // in the local, store in cache
            if (AllocaInst * AI = dyn_cast<AllocaInst>(LI->getPointerOperand())){
              ValueCache[Inst] = getAddrForDeref(LI->getPointerOperand(),ValueCache,DL, tab_level+1);
            }
            else{  //if this is not an alloca see if we have a cached value for the pointer
              std::map<Value *,APInt> ::iterator it = ValueCache.find(LI->getPointerOperand());
              if(it != ValueCache.end()){
                retValue = it->second;
              }
            }
          }
          else if (AllocaInst * AI = dyn_cast<AllocaInst>(Inst)){
            std::map<Value *,APInt> ::iterator it = ValueCache.find(Inst);
            if (it != ValueCache.end()){
              retValue = ValueCache[Inst];
            }else{
            }
          }
          else if (GEPOperator *GEPOp = dyn_cast<GEPOperator>(Inst)){
            APInt Offset =APInt::getNullValue(retValue.getBitWidth());
            if (GEPOp->accumulateConstantOffset(DL,Offset)){
              APInt Base = getAddrForDeref(GEPOp->getOperand(0),ValueCache,DL, tab_level+1);
              if (Base != APInt::getNullValue(retValue.getBitWidth())){
                retValue = Base + Offset;
              }
            }
          }
          else if (GlobalVariable *GV = dyn_cast<GlobalVariable>(Inst)){
            if (GV->hasInitializer()){
                Constant *C = GV->getInitializer();
                if(ConstantInt * CInt =dyn_cast<ConstantInt>(C)){
                  retValue = CInt->getValue();
                }else{
                  retValue = getAddrForDeref(C,ValueCache,DL, tab_level+1);
                }
            }
          }
          return retValue;
    }


    //Adds addresses accessed for all paths which are constant to specific
    //dereference
    bool add_access(Value * V, SmallVector<APInt *, 8> & AccessedAddrs,const DataLayout & DL){
      errs() << "Adding Access for: ";
      if(Constant *C = dyn_cast<Constant>(V)){
        APInt addr = getAddr(C,DL);
        return true;
      }else{
        for(User * U : V->users()){
          if(LoadInst * LI = dyn_cast<LoadInst>(U)){
              return false;
          }else if(StoreInst * SI = dyn_cast<StoreInst>(U)){
            if(SI->getPointerOperand() == V){
              return add_access(SI->getOperand(0),AccessedAddrs,DL);
            }
          }
        }
      }
      return false;
    }

    //The assembly code to elevate an instruction
    void insertElevate( SmallVector<StringRef, 8> &new_strs){
        new_strs.push_back("push {r0}");
        new_strs.push_back("mrs r0, apsr");
        new_strs.push_back("push {r0}");
        new_strs.push_back("mrs r0, control");
        new_strs.push_back("tst r0, 1");  // Z flag will be 1 if r0 AND 1 = 0
        new_strs.push_back("it  ne");  //Check Z=0 (unprivileged is set r0 & 1 =1, Z=0 aka NE)
        new_strs.push_back("svcne 255");
        new_strs.push_back("pop {r0}");
        new_strs.push_back("msr apsr, r0");
        new_strs.push_back("pop {r0}");
        ++InstElevated;

    }

    void insertDropPriv( SmallVector<StringRef, 8> &new_strs){
        new_strs.push_back("push {r0}");
        new_strs.push_back("mrs r0, control");
        new_strs.push_back("orr r0, r0, 1");  // Z flag will be 1 if r0 AND 1 = 0
        new_strs.push_back("msr control, r0");
        new_strs.push_back("pop {r0}");

    }

    InlineAsm * getMemoryElevateAsm(){
        //std::string constraints = "~{r3}";
        std::string asm_str =
            "push {r0}\n\t mrs r0, apsr\n\t push {r0}\n\t mrs r0, control\n\t tst r0, 1\n\t it  ne \n\t svcne 254 \n\t pop {r0} \n\t msr apsr, r0 \n\t pop {r0} \n\t";

        InlineAsm * Asm = InlineAsm::get(FunctionType::get(Type::getVoidTy(Mod->getContext()),{},false),
                                       asm_str,"~{r0},~{r1},~{r2},~{r3},~{r4},~{r5},~{r6},~{r7},~{r8},~{r9},~{r10},~{r11},~{r12},~{r13},~{r14},~{lr},~{memory}",true);

        //return CallInst::Create(Asm,SmallVector<Value *, 8>{},I);
        //return CallInst::Create(Asm,"asm",I);
        return Asm;
    }

    InlineAsm * getDropPrivileges(){

        std::string asm_str = "push {r0}\n\t mrs r0, control\n\t orr r0, 1\n\t msr control, r0 \n\t pop {r0} \n\t";
        //std::string constraints = "~{r3}";
        InlineAsm * Asm = InlineAsm::get(FunctionType::get(Type::getVoidTy(Mod->getContext()),{},false),
                                       asm_str,"~{r0},~{r1},~{r2},~{r3},~{r4},~{r5},~{r6},~{r7},~{r8},~{r9},~{r10},~{r11},~{r12},~{r13},~{r14},~{lr},~{memory}",true);
            return Asm;
    }

    void insertMemoryAccessElevate(Instruction * Inst, APInt addr){
        IRBuilder<> * IRB;
        Instruction * InsertPt=nullptr;
        InlineAsm * elevate = getMemoryElevateAsm();
        InlineAsm * drop_priv = getDropPrivileges();
        Value * const_addr;
        Type * Ty;
        //CallInst * R;
        IRB = new IRBuilder<>(Mod->getContext());

        errs() <<"========================Before Instrumentation================\n";
        Inst->getParent()->dump();

        IRB->SetInsertPoint(Inst);
        IRB->CreateCall(elevate);
        if(LoadInst * I= dyn_cast<LoadInst>(Inst)){
            errs() << "Load Pointer Changing to use constant\n";
            Ty = I->getPointerOperand()->getType();
            const_addr = IRB->CreateIntToPtr(Constant::getIntegerValue(Type::getInt32Ty(Mod->getContext()),addr),Ty);
            const_addr->dump();
            I->setOperand(0,const_addr);
        }else if(StoreInst * I= dyn_cast<StoreInst>(Inst)){
            errs() << "Store Pointer Changing to use constant\n";
            Ty = I->getPointerOperand()->getType();
            const_addr = IRB->CreateIntToPtr(Constant::getIntegerValue(Type::getInt32Ty(Mod->getContext()),addr),Ty);
            I->setOperand(1,const_addr);
        }

        InsertPt = Inst->getNextNode();
        if(InsertPt)IRB->SetInsertPoint(InsertPt);
        else IRB->SetInsertPoint(Inst->getParent()->getTerminator());
        IRB->CreateCall(drop_priv);
        errs() <<"========================After Instrumentation================\n";
        Inst->getParent()->dump();
        delete IRB;
    }

    //Idenitifies privileged assembly instructions and replaces them with
    //assmebly which first calls the SVC Handler
    bool elevateInstruct(Module &M,SmallVector<InlineAsm *, 8> &PrivInsts){
        DEBUG(errs()<< "------------------Start Inline Assebmly--------------------------\n");
        for (InlineAsm * IA : PrivInsts){
            IA->dump();
            SmallVector<StringRef, 8> asm_strs;
            SmallVector<StringRef, 8> new_strs;

            StringRef asm_ref = IA->getAsmString();
            StringRef new_asm;
            StringRef::size_type loc;
            asm_ref.split(asm_strs,'\n');
            bool modified = false;
            for(StringRef str : asm_strs){
                if (str.startswith_lower("cps")){
                    //errs() <<"CPS:: Adding SVC \n";
                    insertElevate(new_strs);
                    new_strs.push_back(str);
                    insertDropPriv(new_strs);
                    modified = true;
                }
                else if (str.startswith_lower("msr") ){
                    //errs() <<"MSR:: Adding SVC \n";
                    insertElevate(new_strs);
                    new_strs.push_back(str);
                    modified = true;
                    insertDropPriv(new_strs);
                }
                else{
                    new_strs.push_back(str);
                    modified = false;
                }
             }

            if (modified){
                std::string new_asm_cmds;
                for (StringRef str : new_strs){
                    new_asm_cmds +=str.str()+"\n\t";
                }
                InlineAsm * newASM = InlineAsm::get(IA->getFunctionType(),new_asm_cmds,"r,~{memory}",IA->hasSideEffects(),IA->isAlignStack());
                IA->replaceAllUsesWith(newASM);
            }
         }
        return false;
    }

    Constant * userStoresAConstant(Value * V){
        for (User * user: V->users()){
            user->dump();
            if(StoreInst * SI = dyn_cast<StoreInst>(user)){
                if(SI->getType()->isPointerTy()){
                    if(Constant * C = dyn_cast<Constant>(user)){
                        return C;
                    }
                }
            }
        }
        return nullptr;
    }

    Constant * usesConstantAddr(Value * V){

        if (StoreInst * SI = dyn_cast<StoreInst>(V)){
            if (Constant *  C = dyn_cast<Constant>(SI->getPointerOperand())){
                return C;
            }
            else{
                return userStoresAConstant(SI->getPointerOperand());
            }
        }
        else if (LoadInst * LI = dyn_cast<LoadInst>(V)){
            if (Constant *  C = dyn_cast<Constant>(LI->getPointerOperand())){
                return C;
            }
            else{
                return userStoresAConstant(LI->getPointerOperand());
            }
        }
        else if (GEPOperator *GEPOp = dyn_cast<GEPOperator>(V)){
            if (Constant *  C = dyn_cast<Constant>(GEPOp)){
                return C;
            }
        }

        return nullptr;
    }

    bool build_mpu_config(Module &M){
      /*
       * If this checks if the MPURegions File is provided and parses the file.
       * It then creates a function (__rt_mpu_config) that configures the
       * MPU with the specified permissions
      */
      bool main_found=false;
      if ( MPURegionsFile.compare("-")!= 0 ){
        Constant * MPU_PTR;
        Value * R;
        Value * Original_Value;
        Function *Func = M.getFunction("main");
        // Only want to do this on the module that has main
        if(!Func){
            return false;
        }

        //Parse the MPU Config file, emit error there is a parsing problem
        if(!parse_file()) {
            M.getContext().emitError("Parsing permissions file failed");
        }
        std::vector<Type *>  IntParams(1,Type::getInt32Ty(M.getContext()));
        std::vector<Value *>  CallParams(1,ConstantInt::get(Type::getInt32Ty(M.getContext()),1));
        //CallParams[0]=ConstantInt::get(Type::getInt32Ty(M.getContext()),1);
        InlineAsm * Asm = InlineAsm::get(FunctionType::get(Type::getVoidTy(M.getContext()),IntParams,false),
                                        "MSR control, $0", "r,~{memory}",true);
        Asm->dump();
        FunctionType *FT = FunctionType::get(Type::getVoidTy(M.getContext()),false);
        Function * mpu_config_function = Function::Create(FT,Function::ExternalLinkage,"__rt_mpu_config",&M);
        mpu_config_function->addFnAttr("no-virt"); //Do not virtualize this function
        BasicBlock::Create(getGlobalContext(), "entry", mpu_config_function);
        IRBuilder<> *IRB;
        IRB = new IRBuilder<>(M.getContext());
        IRB->SetInsertPoint(&mpu_config_function->getEntryBlock());
        DEBUG(dbgs()<<"Created Entry\n");
        MPU_PTR = ConstantInt::get(Type::getInt32Ty(M.getContext()),0xE000ED94); //MPU Control Register
        MPU_PTR = ConstantExpr::getIntToPtr(MPU_PTR,Type::getInt32PtrTy(M.getContext()));
        DEBUG(dbgs()<<"Created MPU_PTR\n");
        Original_Value = IRB->CreateLoad(MPU_PTR,true);

        //IRB->CreateStore(R,Original_Value);
        DEBUG(dbgs()<<"Saved To Stack\n");
        //disable the MPU
        R = IRB->CreateAnd(Original_Value,0xFFFFFFFE);
        IRB->CreateStore(R,MPU_PTR,true);
        DEBUG(dbgs()<<"Disabled MPU\n");

        DEBUG(dbgs()<<"Adding MPU Regions\n");
        add_mpu_configs(M,IRB);
        //enable MPU
        R = IRB->CreateOr(Original_Value,1);
        IRB->CreateStore(R,MPU_PTR,true);
        IRB->CreateCall(Asm,CallParams);
        IRB->CreateRetVoid();
        DEBUG(dbgs()<<"Reset MPU\n");
        DEBUG(mpu_config_function->dump());
        delete IRB;
      }
      return false;

    }

    bool unprivileged_blocked(RegionsStruct &R, APInt addr,Value * I){
    /* Checks to see if unprivileged code can access the given address with
     * the given MPU configuration
     */
        bool isRead = true; //assume is
        bool isWrite = true; //assume is
        bool canWrite = true;
        bool canRead = true;
        if(R.Valid && !R.isPtr){
            print_region(R);
            APInt top_addr = (APInt(addr.getBitWidth(),1)<<(R.Size+1))+APInt(addr.getBitWidth(),R.Addr);

            if (addr.ult(R.Addr) || addr.uge(top_addr)){
                return false;
            }

            if(LoadInst * LI = dyn_cast<LoadInst>(I)){
                isWrite = false;
                //errs() << "Read Request\n";
            }
            if (StoreInst *SI = dyn_cast<StoreInst>(I)){
                isRead = false;
                //errs() << "Write Request\n";
            }

            switch (R.Permissions){
                case 0:
                case 1:
                case 5:
                    //No Unprivileged Access
                    canWrite = false;
                    canRead = false;
                    //errs() <<"Blocked ?:1 \n\n";
                    return true;
                    break;
                case 2:
                case 7:
                 //Unprivileged Read Only
                    canWrite = false;
                    canRead = true;
                    return true; //Looks like SCB doesn't respect MPU config
                    return isWrite;
                    break;
                case 3:
                //Unprivileged Read/Write
                    canWrite = true;
                    canRead = true;
                    return false;
            default:
                break;
            }//switch

        }//if
        return false;
    }

    bool elevate_instructions(InlineAsm *IA){
        SmallVector<StringRef, 8> asm_strs;
        StringRef asm_ref = IA->getAsmString();
        StringRef::size_type loc;
        asm_ref.split(asm_strs,'\n');
        bool modified = false;
        for(StringRef str : asm_strs){
            if (str.startswith_lower("svcne 254")){
                return true;
            }
        }
        return false;
    }

    bool drop_instructions(InlineAsm *IA){
        SmallVector<StringRef, 8> asm_strs;
        StringRef asm_ref = IA->getAsmString();
        int state = 0;
        StringRef::size_type loc;
        asm_ref.split(asm_strs,'\n');
        bool modified = false;
        for(StringRef str : asm_strs){
            switch (state){
                case 0:
                    if (str.startswith_lower("mrs r0, control")){
                        state = 1;
                    }
                break;
                case 1:
                    if (str.startswith_lower("orr r0, 1")){
                        state = 2;
                    }else{
                        return false;
                    }
                break;
                case 2:
                    if (str.startswith_lower("msr control, r0")){
                        return true;
                    }else{
                        return false;
                    }
                    break;
            }
        }
        return false;
    }

    bool runOnModule(Module &M ) override {
        bool in_elevate_block = false;
        if (!AddEdivertLayer){
            return false;
        }
        SmallVector<InlineAsm *, 8> PrivInsts;

        for (Function & F: M){

            // Add MPU Config
            if ( MPURegionsFile.compare("-")!= 0 ){
              Function * Setup_MPU_Funct;
              IRBuilder<> *IRB;
              if (F.getName().equals("main")){
                IRB = new IRBuilder<>(getGlobalContext());
                IRB->SetInsertPoint(&*F.getEntryBlock().getFirstInsertionPt());  //first instructions of main
                //IRB->SetInsertPoint(F.getEntryBlock().getTerminator());  //if want end of entry block
                Setup_MPU_Funct=cast<Function>(F.getParent()->getFunction("__rt_mpu_config"));
                IRB->CreateCall(Setup_MPU_Funct);
                DEBUG(dbgs()<< "=================== main ==========================\n");
                DEBUG(F.dump());
                DEBUG(dbgs()<< "=================== end main ==========================\n");

              }
            } //End MPU Config

            SmallVector<Value *,8> DerefsWorkListPtr;
            SmallVector<Instruction *,8> DerefsWorkListInst;
           dbgs() << "\n\n\n\n=====================Function:"<<F.getName() <<"==================================\n";
            if(F.hasFnAttribute("no-virt")){
                dbgs()<<"Skipping Function:\n";
                continue;
            }
            for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I){
              if (! in_elevate_block){
                  if(StoreInst * SI = dyn_cast<StoreInst>(&*I)){
                    DerefsWorkListPtr.push_back(SI->getPointerOperand());
                    DerefsWorkListInst.push_back(&*SI);
                  }else if(LoadInst * LI = dyn_cast<LoadInst>(&*I)){
                    DerefsWorkListPtr.push_back(LI->getPointerOperand());
                    DerefsWorkListInst.push_back(&*LI);
                  }
              }
              if(CallInst * call = dyn_cast<CallInst>(&*I)){
                //errs() << "Calls";
                //call->dump();
                if(InlineAsm * IA = dyn_cast_or_null<InlineAsm>(call->getCalledValue())){
                    if (elevate_instructions(IA)){
                         errs() << "Start Elevate Block";
                        in_elevate_block = true;
                    }
                    else if (drop_instructions(IA)){
                        errs() << "End Elevate Block";
                        in_elevate_block = false;
                    }
                  //errs() << "Adding Called Value:";
                  //IA->dump();
                    if(!in_elevate_block){
                        PrivInsts.push_back(IA);
                    }
                }
              }
            }

            std::map<Value *,APInt> ValueCache;
            std::set<APInt> AccessedConsts;

            std::map<Value *,Constant *> Memory;
            for (Instruction * V : DerefsWorkListInst){
              DEBUG(errs() << "\n===========================Checking:============================\n");
              DEBUG(V->dump());
              Constant * C= getAddressAccessed(V,Memory);

              if(C){
                  APInt addr;
                  addr = getAddrForDeref(C,ValueCache,Mod->getDataLayout(),0);
                  if (addr == 0){
                      continue; //Zeros indicates addr not determined
                  }
                  ++NumConstAddrs;
                  for(int i=0;i<NUM_REGIONS;i++){
                      if(unprivileged_blocked(this->regions[i],addr,V)){
                          ++AddrElevated;
                          insertMemoryAccessElevate(V,addr);
                          break;
                          }
                      }
                  }
              }
          }//for Function
        elevateInstruct(M,PrivInsts);
        return true;
    }

    bool printMap(std::map<Value *,Constant *> Memory){
      for (auto it : Memory){
        errs()<<"Addr: ";
        if (it.first)
          it.first->dump();
        else
          errs()<<"nullptr\n";
        errs()<<"    Data:";
        if(it.second){
          it.second->dump();
        }
        else{
          errs()<<"nullptr\n";
        }
      }
      return true;
    }


   void getAnalysisUsage(AnalysisUsage &AU) const override {

    }

  };

}


char InsertVirtualizationLayer::ID = 0;
INITIALIZE_PASS_BEGIN(InsertVirtualizationLayer, "insert-virtualization", "Adds Virtualization Layer to program",false, false)

INITIALIZE_PASS_END(InsertVirtualizationLayer, "insert-virtualization", "Adds Virtualization Layer to program",false, false)

ModulePass *llvm::createInsertVirtualizationLayerPass(){
  DEBUG(errs() << "Creating InsertVirtualizationLayer" <<"\n");
  return new InsertVirtualizationLayer();
}
