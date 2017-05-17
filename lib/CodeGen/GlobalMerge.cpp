//===-- GlobalMerge.cpp - Internal globals merging  -----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
// This pass merges globals with internal linkage into one. This way all the
// globals which were merged into a biggest one can be addressed using offsets
// from the same base pointer (no need for separate base pointer for each of the
// global). Such a transformation can significantly reduce the register pressure
// when many globals are involved.
//
// For example, consider the code which touches several global variables at
// once:
//
// static int foo[N], bar[N], baz[N];
//
// for (i = 0; i < N; ++i) {
//    foo[i] = bar[i] * baz[i];
// }
//
//  On ARM the addresses of 3 arrays should be kept in the registers, thus
//  this code has quite large register pressure (loop body):
//
//  ldr     r1, [r5], #4
//  ldr     r2, [r6], #4
//  mul     r1, r2, r1
//  str     r1, [r0], #4
//
//  Pass converts the code to something like:
//
//  static struct {
//    int foo[N];
//    int bar[N];
//    int baz[N];
//  } merged;
//
//  for (i = 0; i < N; ++i) {
//    merged.foo[i] = merged.bar[i] * merged.baz[i];
//  }
//
//  and in ARM code this becomes:
//
//  ldr     r0, [r5, #40]
//  ldr     r1, [r5, #80]
//  mul     r0, r1, r0
//  str     r0, [r5], #4
//
//  note that we saved 2 registers here almostly "for free".
//
// However, merging globals can have tradeoffs:
// - it confuses debuggers, tools, and users
// - it makes linker optimizations less useful (order files, LOHs, ...)
// - it forces usage of indexed addressing (which isn't necessarily "free")
// - it can increase register pressure when the uses are disparate enough.
//
// We use heuristics to discover the best global grouping we can (cf cl::opts).
// ===---------------------------------------------------------------------===//

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallBitVector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetLowering.h"
#include "llvm/Target/TargetLoweringObjectFile.h"
#include "llvm/Target/TargetSubtargetInfo.h"
#include "llvm/Support/RandomNumberGenerator.h"
#include <algorithm>
using namespace llvm;

#define DEBUG_TYPE "global-merge"

// FIXME: This is only useful as a last-resort way to disable the pass.
static cl::opt<bool>
EnableGlobalMerge("enable-global-merge", cl::Hidden,
                  cl::desc("Enable the global merge pass"),
                  cl::init(true));

static cl::opt<bool> GlobalMergeGroupByUse(
    "global-merge-group-by-use", cl::Hidden,
    cl::desc("Improve global merge pass to look at uses"), cl::init(true));

static cl::opt<bool> GlobalMergeIgnoreSingleUse(
    "global-merge-ignore-single-use", cl::Hidden,
    cl::desc("Improve global merge pass to ignore globals only used alone"),
    cl::init(true));

static cl::opt<bool>
EnableGlobalMergeOnConst("global-merge-on-const", cl::Hidden,
                         cl::desc("Enable global merge pass on constants"),
                         cl::init(false));

static cl::opt<unsigned>
MaxAddTraps("global-merge-max-add-traps",
      cl::desc("Enable global adding traps after none constant arrays"),
                    cl::init(0));

/*static cl::opt<bool>
EnableRandomizeGlobals("global-merge-randomize",
      cl::desc("Randomize Location of Global Variables"),
                    cl::init(false));
*/
static cl::opt<unsigned>
OptionGlobalMaxPadSize("global-merge-pad-data",
                       cl::desc("Max Number of bytes to add as padding"),
                       cl::init(0));

static cl::opt<unsigned>
OptionGlobalMaxDataSectionPad("global-merge-max-data-section-pad",
                              cl::desc("Max Number of bytes that can be added to the data section for padding"),
                              cl::init(0));

STATISTIC(NumTrapsAdded     , "Number of globals buffer traps added");
STATISTIC(DataPadAdded      , "Number of uint32 variables add to .data");
STATISTIC(BSSPadAdded      , "Number of uint32 variables add to .bss");
STATISTIC(PreStackPadAdded      , "Number of uint32 variables added to .pre_stack_pad");
STATISTIC(PreUnsafeStackPad      , "Number of uint32 variables added to .pre_unsafestack_pad");

// FIXME: this could be a transitional option, and we probably need to remove
// it if only we are sure this optimization could always benefit all targets.
static cl::opt<cl::boolOrDefault>
EnableGlobalMergeOnExternal("global-merge-on-external", cl::Hidden,
     cl::desc("Enable global merge pass on external linkage"));

STATISTIC(NumMerged, "Number of globals merged");
namespace {
  class GlobalMerge : public FunctionPass {
    const TargetMachine *TM;
    // FIXME: Infer the maximum possible offset depending on the actual users
    // (these max offsets are different for the users inside Thumb or ARM
    // functions), see the code that passes in the offset in the ARM backend
    // for more information.
    unsigned MaxOffset;

    /// Whether we should try to optimize for size only.
    /// Currently, this applies a dead simple heuristic: only consider globals
    /// used in minsize functions for merging.
    /// FIXME: This could learn about optsize, and be used in the cost model.
    bool OnlyOptimizeForSize;

    /// Whether we should merge global variables that have external linkage.
    bool MergeExternalGlobals;

    bool doMerge(SmallVectorImpl<GlobalVariable*> &Globals,
                 Module &M, bool isConst, unsigned AddrSpace) ;
    /// \brief Merge everything in \p Globals for which the corresponding bit
    /// in \p GlobalSet is set.
    bool doMerge(const SmallVectorImpl<GlobalVariable *> &Globals,
                 const BitVector &GlobalSet, Module &M, bool isConst,
                 unsigned AddrSpace) ;

    /// \brief Check if the given variable has been identified as must keep
    /// \pre setMustKeepGlobalVariables must have been called on the Module that
    ///      contains GV
    bool isMustKeepGlobalVariable(const GlobalVariable *GV) const {
      return MustKeepGlobalVariables.count(GV);
    }

    /// Collect every variables marked as "used" or used in a landing pad
    /// instruction for this Module.
    void setMustKeepGlobalVariables(Module &M);

    /// Collect every variables marked as "used"
    void collectUsedGlobalVariables(Module &M);

    /// Keep track of the GlobalVariable that must not be merged away
    SmallPtrSet<const GlobalVariable *, 16> MustKeepGlobalVariables;

  public:
    static char ID;             // Pass identification, replacement for typeid.
    explicit GlobalMerge(const TargetMachine *TM = nullptr,
                         unsigned MaximalOffset = 0,
                         bool OnlyOptimizeForSize = false,
                         bool MergeExternalGlobals = false)
        : FunctionPass(ID), TM(TM), MaxOffset(MaximalOffset),
          OnlyOptimizeForSize(OnlyOptimizeForSize),
          MergeExternalGlobals(MergeExternalGlobals) {
      initializeGlobalMergePass(*PassRegistry::getPassRegistry());
    }

    bool doInitialization(Module &M) override;
    bool runOnFunction(Function &F) override;
    bool doFinalization(Module &M) override;

    //Used by doMerge to insert traps after arrays
    void insertTrap(Module &M, std::vector<GlobalVariable *> &GVs);
    void addTraps(Module &M);
    void shuffleGlobals (Module & M);

    const char *getPassName() const override {
      return "Merge internal globals";
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesCFG();
      FunctionPass::getAnalysisUsage(AU);
    }
  private:
    RandomNumberGenerator * RandGen;
    int  NumTraps;
    GlobalVariable *  LastTrap;
  };
} // end anonymous namespace

char GlobalMerge::ID = 0;
INITIALIZE_PASS_BEGIN(GlobalMerge, "global-merge", "Merge global variables",
                      false, false)
INITIALIZE_PASS_END(GlobalMerge, "global-merge", "Merge global variables",
                    false, false)


void GlobalMerge::insertTrap(Module &M, std::vector<GlobalVariable *> &GVs){
    DEBUG(dbgs()<<"[global-merge] Inserting Trap------------------------\n");
    Constant * NewInit;
    Type * TrapType=LastTrap->getType()->getElementType();
    GlobalVariable * NewTrap =new GlobalVariable(M,TrapType,false, GlobalVariable::InternalLinkage,
        ConstantExpr::getNullValue(TrapType),"__data_traps_node");
    NewTrap->setSection(".data");
    NewTrap->setAlignment(4);
    DEBUG(dbgs()<<"New Trap:\t\t";NewTrap->dump(); );

    //Change initializer of LastTrap to Point to this one
    NewInit= ConstantExpr::getBitCast(NewTrap,LastTrap->getType()->getElementType());
    LastTrap->setInitializer(NewInit);
    LastTrap->setSection(".data");


    //Insert LastTrap to merged variables
    GVs.push_back(LastTrap);

    DEBUG(dbgs()<<"Inserted Trap:\t";LastTrap->dump(); );
    //MergedGVs.push_back(LastTrap);
    NumTrapsAdded++;
    LastTrap=NewTrap;
    DEBUG(dbgs()<<"[global-merge] Done Inserting Trap------------------------\n");
}

void GlobalMerge::addTraps(Module &M){
    //Only the default address space gets trapped
    // for now mark as used to keep from moving them
    Type *Int32Ty = Type::getInt32Ty(M.getContext());
    //Go though globals and identify all arrays or other types we want to trap
    std::vector<GlobalVariable *> GlobalArrays;

    for (auto &GV : M.globals()){
      CompositeType *CT = dyn_cast<CompositeType>(GV.getType());
      if (GV.getType()->getAddressSpace() != 0 || GV.hasSection()){
        continue;
      }
      if (GV.isConstant()){
        continue;
      }
      assert(CT && "Global variable is not a compositetype!");
      DEBUG(dbgs()<<"Global Varibale is: "<<GV.getName()
                 << " Num Contained Types? : "<<CT->getNumContainedTypes()
                 << " Contained Type:  "<<CT->getContainedType(0)->isArrayTy()
                  //<< " Type : "<< isa<ArrayType>(GV)
                  <<"\n");
      DEBUG(dbgs()<<"Type at 0 \n");
      DEBUG(CT->getContainedType(0)->dump());
      DEBUG(dbgs()<<"Var Dump\n");
      DEBUG(GV.dump());

      if (CT->getContainedType(0)->isArrayTy()){
        DEBUG(dbgs()<<"\tIs Array: "<<"\n");
        GlobalArrays.push_back(&GV);
      }
    }

    //Drop Until less than Max Traps
    while(GlobalArrays.size()> (MaxAddTraps/2)){
      int remove_index = ((*RandGen)())%GlobalArrays.size();
      DEBUG(dbgs()<<"Removing Index "<<remove_index<<"\n");
      GlobalArrays.erase(GlobalArrays.begin()+remove_index);
    }

    //for each GlobalArray
    for (GlobalVariable *GV : GlobalArrays){
      std::vector<GlobalVariable *> GVs;
      std::vector<Type*> Tys;
      std::vector<Constant*> Inits;

      //Add the Traps and array to a list
      insertTrap(M,GVs);
      GVs.push_back(GV);
      insertTrap(M,GVs);


      PointerType *PT = dyn_cast<PointerType>(GV->getType());
      assert(PT && "Global variable is not a pointer!");
      unsigned AddrSpace = PT->getAddressSpace();

      for(unsigned i=0 ;i <GVs.size();i++){
        Tys.push_back(GVs.at(i)->getType()->getElementType());
        Inits.push_back(GVs.at(i)->getInitializer());
      }

      //Create Struct with var and traps
      StructType *MergedTy = StructType::get(M.getContext(), Tys);
      Constant *MergedInit = ConstantStruct::get(MergedTy, Inits);

      GlobalVariable *MergedGV = new GlobalVariable(
          M, MergedTy, GV->isConstant(), GlobalValue::PrivateLinkage, MergedInit,
          "_TrappedGlobals", nullptr, GlobalVariable::NotThreadLocal, AddrSpace);
      MergedGV->setSection(".data");
      MergedGV->setAlignment(4);

      for (unsigned i =0; i<GVs.size(); i++){
        GlobalValue::LinkageTypes Linkage = GVs.at(i)->getLinkage();
        std::string Name = GVs.at(i)->getName();

        Constant *Idx[2] = {
          ConstantInt::get(Int32Ty, 0),
          ConstantInt::get(Int32Ty, i)
        };

        Constant *GEP =
            ConstantExpr::getInBoundsGetElementPtr(MergedTy, MergedGV, Idx);
        GVs.at(i)->replaceAllUsesWith(GEP);
        GVs.at(i)->eraseFromParent();



        // When the linkage is not internal we must emit an alias for the original
        // variable name as it may be accessed from another object. On non-Mach-O
        // we can also emit an alias for internal linkage as it's safe to do so.
        // It's not safe on Mach-O as the alias (and thus the portion of the
        // MergedGlobals variable) may be dead stripped at link time.
        if (Linkage != GlobalValue::InternalLinkage ||
            !TM->getTargetTriple().isOSBinFormatMachO()) {

          //aliasing causes double counting of these vars in arm-none-eabi-size
          GlobalAlias::create(Tys[i], AddrSpace, Linkage, Name, GEP, &M);

        }
      }
      DEBUG(MergedGV->dump());
    }

    /* update count */

    GlobalVariable * TrapCount=M.getNamedGlobal("__data_traps_count");
    Constant * Init = ConstantInt::get(TrapCount->getType()->getElementType(),NumTrapsAdded);
    TrapCount->setInitializer(Init);
    //NumTrapsAdded=NumTraps;

    /* last data_trap_key */
    unsigned int rand_num = ((*RandGen)())%0xFFFFFFFF;
    GlobalVariable * TrapKey=M.getNamedGlobal("__data_traps_key");
    Init = ConstantInt::get(TrapKey->getType()->getElementType(),rand_num);
    TrapKey->setInitializer(Init);

    /* last data_trap_key */
    GlobalVariable * TrapSecret=M.getNamedGlobal("__data_traps_secret_value");
    TrapSecret->setSection(".data");
    Init = ConstantInt::get(TrapSecret->getType()->getElementType(),((*RandGen)())%0xFFFFFFFF);
    TrapSecret->setInitializer(Init);
}

bool GlobalMerge::doMerge(SmallVectorImpl<GlobalVariable*> &Globals,
                          Module &M, bool isConst, unsigned AddrSpace)  {
  auto &DL = M.getDataLayout();
  // FIXME: Find better heuristics
  if (!OptionGlobalMaxPadSize){
    DEBUG(dbgs()<<"Not Randomizing Globals\n");
    std::stable_sort(Globals.begin(), Globals.end(),
                   [&DL](const GlobalVariable *GV1, const GlobalVariable *GV2) {
                     return DL.getTypeAllocSize(GV1->getValueType()) <
                            DL.getTypeAllocSize(GV2->getValueType());
                   });
  }

  // If we want to just blindly group all globals together, do so.
  if (!GlobalMergeGroupByUse || OptionGlobalMaxPadSize) {
  //if (!GlobalMergeGroupByUse){
    DEBUG(dbgs()<<"Randomizing Globals \n");
    BitVector AllGlobals(Globals.size());
    AllGlobals.set();
    return doMerge(Globals, AllGlobals, M, isConst, AddrSpace);
  }

  // If we want to be smarter, look at all uses of each global, to try to
  // discover all sets of globals used together, and how many times each of
  // these sets occurred.
  //
  // Keep this reasonably efficient, by having an append-only list of all sets
  // discovered so far (UsedGlobalSet), and mapping each "together-ness" unit of
  // code (currently, a Function) to the set of globals seen so far that are
  // used together in that unit (GlobalUsesByFunction).
  //
  // When we look at the Nth global, we now that any new set is either:
  // - the singleton set {N}, containing this global only, or
  // - the union of {N} and a previously-discovered set, containing some
  //   combination of the previous N-1 globals.
  // Using that knowledge, when looking at the Nth global, we can keep:
  // - a reference to the singleton set {N} (CurGVOnlySetIdx)
  // - a list mapping each previous set to its union with {N} (EncounteredUGS),
  //   if it actually occurs.

  // We keep track of the sets of globals used together "close enough".
  struct UsedGlobalSet {
    UsedGlobalSet(size_t Size) : Globals(Size), UsageCount(1) {}
    BitVector Globals;
    unsigned UsageCount;
  };

  // Each set is unique in UsedGlobalSets.
  std::vector<UsedGlobalSet> UsedGlobalSets;

  // Avoid repeating the create-global-set pattern.
  auto CreateGlobalSet = [&]() -> UsedGlobalSet & {
    UsedGlobalSets.emplace_back(Globals.size());
    return UsedGlobalSets.back();
  };

  // The first set is the empty set.
  CreateGlobalSet().UsageCount = 0;

  // We define "close enough" to be "in the same function".
  // FIXME: Grouping uses by function is way too aggressive, so we should have
  // a better metric for distance between uses.
  // The obvious alternative would be to group by BasicBlock, but that's in
  // turn too conservative..
  // Anything in between wouldn't be trivial to compute, so just stick with
  // per-function grouping.

  // The value type is an index into UsedGlobalSets.
  // The default (0) conveniently points to the empty set.
  DenseMap<Function *, size_t /*UsedGlobalSetIdx*/> GlobalUsesByFunction;

  // Now, look at each merge-eligible global in turn.

  // Keep track of the sets we already encountered to which we added the
  // current global.
  // Each element matches the same-index element in UsedGlobalSets.
  // This lets us efficiently tell whether a set has already been expanded to
  // include the current global.
  std::vector<size_t> EncounteredUGS;

  for (size_t GI = 0, GE = Globals.size(); GI != GE; ++GI) {
    GlobalVariable *GV = Globals[GI];

    // Reset the encountered sets for this global...
    std::fill(EncounteredUGS.begin(), EncounteredUGS.end(), 0);
    // ...and grow it in case we created new sets for the previous global.
    EncounteredUGS.resize(UsedGlobalSets.size());

    // We might need to create a set that only consists of the current global.
    // Keep track of its index into UsedGlobalSets.
    size_t CurGVOnlySetIdx = 0;

    // For each global, look at all its Uses.
    for (auto &U : GV->uses()) {
      // This Use might be a ConstantExpr.  We're interested in Instruction
      // users, so look through ConstantExpr...
      Use *UI, *UE;
      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(U.getUser())) {
        if (CE->use_empty())
          continue;
        UI = &*CE->use_begin();
        UE = nullptr;
      } else if (isa<Instruction>(U.getUser())) {
        UI = &U;
        UE = UI->getNext();
      } else {
        continue;
      }

      // ...to iterate on all the instruction users of the global.
      // Note that we iterate on Uses and not on Users to be able to getNext().
      for (; UI != UE; UI = UI->getNext()) {
        Instruction *I = dyn_cast<Instruction>(UI->getUser());
        if (!I)
          continue;

        Function *ParentFn = I->getParent()->getParent();

        // If we're only optimizing for size, ignore non-minsize functions.
        if (OnlyOptimizeForSize && !ParentFn->optForMinSize())
          continue;

        size_t UGSIdx = GlobalUsesByFunction[ParentFn];

        // If this is the first global the basic block uses, map it to the set
        // consisting of this global only.
        if (!UGSIdx) {
          // If that set doesn't exist yet, create it.
          if (!CurGVOnlySetIdx) {
            CurGVOnlySetIdx = UsedGlobalSets.size();
            CreateGlobalSet().Globals.set(GI);
          } else {
            ++UsedGlobalSets[CurGVOnlySetIdx].UsageCount;
          }

          GlobalUsesByFunction[ParentFn] = CurGVOnlySetIdx;
          continue;
        }

        // If we already encountered this BB, just increment the counter.
        if (UsedGlobalSets[UGSIdx].Globals.test(GI)) {
          ++UsedGlobalSets[UGSIdx].UsageCount;
          continue;
        }

        // If not, the previous set wasn't actually used in this function.
        --UsedGlobalSets[UGSIdx].UsageCount;

        // If we already expanded the previous set to include this global, just
        // reuse that expanded set.
        if (size_t ExpandedIdx = EncounteredUGS[UGSIdx]) {
          ++UsedGlobalSets[ExpandedIdx].UsageCount;
          GlobalUsesByFunction[ParentFn] = ExpandedIdx;
          continue;
        }

        // If not, create a new set consisting of the union of the previous set
        // and this global.  Mark it as encountered, so we can reuse it later.
        GlobalUsesByFunction[ParentFn] = EncounteredUGS[UGSIdx] =
            UsedGlobalSets.size();

        UsedGlobalSet &NewUGS = CreateGlobalSet();
        NewUGS.Globals.set(GI);
        NewUGS.Globals |= UsedGlobalSets[UGSIdx].Globals;
      }
    }
  }

  // Now we found a bunch of sets of globals used together.  We accumulated
  // the number of times we encountered the sets (i.e., the number of blocks
  // that use that exact set of globals).
  //
  // Multiply that by the size of the set to give us a crude profitability
  // metric.
  std::sort(UsedGlobalSets.begin(), UsedGlobalSets.end(),
            [](const UsedGlobalSet &UGS1, const UsedGlobalSet &UGS2) {
              return UGS1.Globals.count() * UGS1.UsageCount <
                     UGS2.Globals.count() * UGS2.UsageCount;
            });

  // We can choose to merge all globals together, but ignore globals never used
  // with another global.  This catches the obviously non-profitable cases of
  // having a single global, but is aggressive enough for any other case.
  if (GlobalMergeIgnoreSingleUse) {
    BitVector AllGlobals(Globals.size());
    for (size_t i = 0, e = UsedGlobalSets.size(); i != e; ++i) {
      const UsedGlobalSet &UGS = UsedGlobalSets[e - i - 1];
      if (UGS.UsageCount == 0)
        continue;
      if (UGS.Globals.count() > 1)
        AllGlobals |= UGS.Globals;
    }
    return doMerge(Globals, AllGlobals, M, isConst, AddrSpace);
  }

  // Starting from the sets with the best (=biggest) profitability, find a
  // good combination.
  // The ideal (and expensive) solution can only be found by trying all
  // combinations, looking for the one with the best profitability.
  // Don't be smart about it, and just pick the first compatible combination,
  // starting with the sets with the best profitability.
  BitVector PickedGlobals(Globals.size());
  bool Changed = false;

  for (size_t i = 0, e = UsedGlobalSets.size(); i != e; ++i) {
    const UsedGlobalSet &UGS = UsedGlobalSets[e - i - 1];
    if (UGS.UsageCount == 0)
      continue;
    if (PickedGlobals.anyCommon(UGS.Globals))
      continue;
    PickedGlobals |= UGS.Globals;
    // If the set only contains one global, there's no point in merging.
    // Ignore the global for inclusion in other sets though, so keep it in
    // PickedGlobals.
    if (UGS.Globals.count() < 2)
      continue;
    Changed |= doMerge(Globals, UGS.Globals, M, isConst, AddrSpace);
  }

  return Changed;
}

bool GlobalMerge::doMerge(const SmallVectorImpl<GlobalVariable *> &Globals,
                          const BitVector &GlobalSet, Module &M, bool isConst,
                          unsigned AddrSpace)  {
  assert(Globals.size() > 1);

  Type *Int32Ty = Type::getInt32Ty(M.getContext());
  auto &DL = M.getDataLayout();

  DEBUG(dbgs() << " Trying to merge set, starts with #"
               << GlobalSet.find_first() << "\n" );


  ssize_t i = GlobalSet.find_first();
  while (i != -1) {
    DEBUG(dbgs()<<"Merging Vars" <<"\n");
    ssize_t j = 0;
    uint64_t MergedSize = 0;
    std::vector<Type*> Tys;
    std::vector<Constant*> Inits;
    bool last_was_array =false;

    for (j = i; j != -1; j = GlobalSet.find_next(j)) {
      Type *Ty = Globals[j]->getValueType();
      MergedSize += DL.getTypeAllocSize(Ty);
      if (MergedSize > MaxOffset) {
          break;
      }
      Tys.push_back(Ty);
      Inits.push_back(Globals[j]->getInitializer());
      last_was_array = false;

    }

    StructType *MergedTy = StructType::get(M.getContext(), Tys);
    Constant *MergedInit = ConstantStruct::get(MergedTy, Inits);

    GlobalVariable *MergedGV = new GlobalVariable(
        M, MergedTy, isConst, GlobalValue::PrivateLinkage, MergedInit,
        "_MergedGlobals", nullptr, GlobalVariable::NotThreadLocal, AddrSpace);

    for (ssize_t k = i, idx = 0; k != j; k = GlobalSet.find_next(k), ++idx) {
      GlobalValue::LinkageTypes Linkage = Globals[k]->getLinkage();
      std::string Name = Globals[k]->getName();

      Constant *Idx[2] = {
        ConstantInt::get(Int32Ty, 0),
        ConstantInt::get(Int32Ty, idx),
      };
      Constant *GEP =
          ConstantExpr::getInBoundsGetElementPtr(MergedTy, MergedGV, Idx);
      Globals[k]->replaceAllUsesWith(GEP);
      Globals[k]->eraseFromParent();

      // When the linkage is not internal we must emit an alias for the original
      // variable name as it may be accessed from another object. On non-Mach-O
      // we can also emit an alias for internal linkage as it's safe to do so.
      // It's not safe on Mach-O as the alias (and thus the portion of the
      // MergedGlobals variable) may be dead stripped at link time.
      if (Linkage != GlobalValue::InternalLinkage ||
          !TM->getTargetTriple().isOSBinFormatMachO()) {
        GlobalAlias::create(Tys[idx], AddrSpace, Linkage, Name, GEP, &M);
      }

      NumMerged++;
    }
    i = j;
  }

  return true;
}

void GlobalMerge::collectUsedGlobalVariables(Module &M) {
  // Extract global variables from llvm.used array
  const GlobalVariable *GV = M.getGlobalVariable("llvm.used");
  if (!GV || !GV->hasInitializer()) return;

  // Should be an array of 'i8*'.
  const ConstantArray *InitList = cast<ConstantArray>(GV->getInitializer());

  for (unsigned i = 0, e = InitList->getNumOperands(); i != e; ++i)
    if (const GlobalVariable *G =
        dyn_cast<GlobalVariable>(InitList->getOperand(i)->stripPointerCasts()))
      MustKeepGlobalVariables.insert(G);
}

void GlobalMerge::setMustKeepGlobalVariables(Module &M) {
  collectUsedGlobalVariables(M);

  for (Module::iterator IFn = M.begin(), IEndFn = M.end(); IFn != IEndFn;
       ++IFn) {
    for (Function::iterator IBB = IFn->begin(), IEndBB = IFn->end();
         IBB != IEndBB; ++IBB) {
      // Follow the invoke link to find the landing pad instruction
      const InvokeInst *II = dyn_cast<InvokeInst>(IBB->getTerminator());
      if (!II) continue;

      const LandingPadInst *LPInst = II->getUnwindDest()->getLandingPadInst();
      // Look for globals in the clauses of the landing pad instruction
      for (unsigned Idx = 0, NumClauses = LPInst->getNumClauses();
           Idx != NumClauses; ++Idx)
        if (const GlobalVariable *GV =
            dyn_cast<GlobalVariable>(LPInst->getClause(Idx)
                                     ->stripPointerCasts()))
          MustKeepGlobalVariables.insert(GV);
    }
  }
}

void GlobalMerge::shuffleGlobals (Module & M){

  SmallVector<GlobalVariable *, 10> sv;
  DEBUG(dbgs()<<"Shuffling Globals\n" << "\n");
  for (iplist<GlobalVariable>::iterator itr=M.getGlobalList().begin();
            itr!=M.getGlobalList().end();){
    GlobalVariable * G = M.getGlobalList().remove(itr);
    //DEBUG(dbgs()<<G->getName() << "\n");
    sv.push_back(G);
    //M.getFunctionList().remove(&F);

  }

  //DEBUG(dbgs()<<"Shuffled Functions\n" << "\n");
  for (size_t i=sv.size()-1;i>0;i--){
    size_t j=((*RandGen)())%i;
    std::swap(sv[i],sv[j]);

  }

  for (GlobalVariable *G :sv){
    M.getGlobalList().push_back(G);
    //DEBUG(dbgs()<<G->getName() << "\n");
  }
}

bool GlobalMerge::doInitialization(Module &M) {

  if (!EnableGlobalMerge)
    return false;

  RandGen=M.createRNG(this);


  auto &DL = M.getDataLayout();
  DenseMap<unsigned, SmallVector<GlobalVariable*, 16> > Globals, ConstGlobals,
                                                        BSSGlobals;
  bool Changed = false;
  PreUnsafeStackPad = 0;
  NumTrapsAdded= 0;
  PreStackPadAdded = 0;
  DataPadAdded = 0;
  BSSPadAdded = 0;


  if (MaxAddTraps){
    DEBUG(dbgs()<< "In Global Merge\n");
    GlobalVariable * TrapHead;
    Constant * HeadNewInit;
    TrapHead=dyn_cast_or_null<GlobalVariable>(M.getOrInsertGlobal("__data_traps_head",Type::getInt32PtrTy(M.getContext())));
    DEBUG(dbgs()<< "global-merge: ");
    DEBUG(TrapHead->dump());
    LastTrap =new GlobalVariable(M,TrapHead->getType()->getElementType(),
                   false, GlobalVariable::InternalLinkage,
        ConstantExpr::getNullValue(TrapHead->getType()->getElementType()),"__data_traps_node");
    LastTrap->setSection(".data");
    NumTraps=1;  //Added Last Trap, + Head
    HeadNewInit= ConstantExpr::getBitCast(LastTrap,LastTrap->getType()->getElementType());
    TrapHead->setInitializer(HeadNewInit);
    DEBUG(TrapHead->dump());

    addTraps(M);
    shuffleGlobals(M);

  }

  if (OptionGlobalMaxPadSize!=0){
    int max_data_pads;
    if(!OptionGlobalMaxDataSectionPad || OptionGlobalMaxDataSectionPad> OptionGlobalMaxPadSize){
      max_data_pads = OptionGlobalMaxPadSize;
    }else{
      max_data_pads =OptionGlobalMaxDataSectionPad ;
    }

    int num_pads = 0;
    int data_pads = (*RandGen)()% (max_data_pads/4);
    num_pads += data_pads;
    int bss_pads = (*RandGen)()%((OptionGlobalMaxPadSize - num_pads)/4);
    num_pads += bss_pads;

    int pre_stack_pad = (*RandGen)()%((OptionGlobalMaxPadSize - num_pads)/4);
    num_pads += pre_stack_pad;


    int pre_unsafestack_pad = (*RandGen)()%((OptionGlobalMaxPadSize - num_pads)/4);
    num_pads += pre_unsafestack_pad;


    for(int i =0;i<pre_stack_pad;i++){
      //DEBUG(dbgs()<<"Creating pre_stack_pad Vars\n");
      GlobalVariable *PadGV = new GlobalVariable(M,Type::getInt32Ty(M.getContext()),
                       false, GlobalVariable::InternalLinkage,
                       ConstantInt::get(Type::getInt32Ty(M.getContext()),0),"__pre_stack_pad");
      PadGV->setSection(".prestack");
    }

    for(int i =0;i<pre_unsafestack_pad;i++){
      //DEBUG(dbgs()<<"Creating pre_stack_pad Vars\n");
      GlobalVariable *PadGV = new GlobalVariable(M,Type::getInt32Ty(M.getContext()),
                       false, GlobalVariable::InternalLinkage,
                       ConstantInt::get(Type::getInt32Ty(M.getContext()),0),"__pre_unsafestack_pad");
      PadGV->setSection(".preunsafestack");
    }

    for(int i =0;i<bss_pads;i++){
      //DEBUG(dbgs()<<"Creating BSS Vars\n");
      GlobalVariable *PadGV = new GlobalVariable(M,Type::getInt32Ty(M.getContext()),
                       false, GlobalVariable::InternalLinkage,
                       ConstantInt::get(Type::getInt32Ty(M.getContext()),0),"__bss_pad");
      PadGV->setSection(".bss");
    }
    //Data Pads
    for(int i =0;i<data_pads;i++){
      int rand = (*RandGen)() %0xFFFFFFFF;
      //DEBUG(dbgs()<<"Creating Data Vars\n");
      GlobalVariable *PadGV = new GlobalVariable(M,Type::getInt32Ty(M.getContext()),
                       false, GlobalVariable::InternalLinkage,
                     ConstantInt::get(Type::getInt32Ty(M.getContext()),rand),"__data_pad");
      PadGV->setSection(".data");

    }
    //Update Stats
    PreUnsafeStackPad = pre_unsafestack_pad;
    PreStackPadAdded = pre_stack_pad;
    DataPadAdded = data_pads;
    BSSPadAdded = bss_pads;
   shuffleGlobals(M);

  }



  setMustKeepGlobalVariables(M);

  // Grab all non-const globals.
  for (auto &GV : M.globals()) {
    // Merge is safe for "normal" internal or external globals only
    if (GV.isDeclaration() || GV.isThreadLocal() || GV.hasSection())
      continue;

    if (!(MergeExternalGlobals && GV.hasExternalLinkage()) &&
        !GV.hasInternalLinkage())
      continue;

    PointerType *PT = dyn_cast<PointerType>(GV.getType());
    assert(PT && "Global variable is not a pointer!");

    unsigned AddressSpace = PT->getAddressSpace();

    // Ignore fancy-aligned globals for now.
    unsigned Alignment = DL.getPreferredAlignment(&GV);
    Type *Ty = GV.getValueType();
    if (Alignment > DL.getABITypeAlignment(Ty))
      continue;

    // Ignore all 'special' globals.
    if (GV.getName().startswith("llvm.") ||
        GV.getName().startswith(".llvm."))
      continue;

    // Ignore all "required" globals:
    if (isMustKeepGlobalVariable(&GV))
      continue;

    if (DL.getTypeAllocSize(Ty) < MaxOffset) {
      if (TargetLoweringObjectFile::getKindForGlobal(&GV, *TM).isBSSLocal())
        BSSGlobals[AddressSpace].push_back(&GV);
      else if (GV.isConstant())
        ConstGlobals[AddressSpace].push_back(&GV);
      else
        Globals[AddressSpace].push_back(&GV);
    }
  }

  for (auto &P : Globals)
    if (P.second.size() > 1)
      Changed |= doMerge(P.second, M, false, P.first);

  for (auto &P : BSSGlobals)
    if (P.second.size() > 1)
      Changed |= doMerge(P.second, M, false, P.first);

  if (EnableGlobalMergeOnConst)
    for (auto &P : ConstGlobals)
      if (P.second.size() > 1)
        Changed |= doMerge(P.second, M, true, P.first);

  return Changed;
}

bool GlobalMerge::runOnFunction(Function &F) {
  return false;
}

bool GlobalMerge::doFinalization(Module &M) {
  MustKeepGlobalVariables.clear();
  return false;
}

Pass *llvm::createGlobalMergePass(const TargetMachine *TM, unsigned Offset,
                                  bool OnlyOptimizeForSize,
                                  bool MergeExternalByDefault) {
  bool MergeExternal = (EnableGlobalMergeOnExternal == cl::BOU_UNSET) ?
    MergeExternalByDefault : (EnableGlobalMergeOnExternal == cl::BOU_TRUE);
  return new GlobalMerge(TM, Offset, OnlyOptimizeForSize, MergeExternal);
}
