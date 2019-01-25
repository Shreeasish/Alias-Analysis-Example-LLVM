
#include "llvm/ADT/SparseBitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/CFLSteensAliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/ScalarEvolutionAliasAnalysis.h"
#include "llvm/Analysis/ScopedNoAliasAA.h"

#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/Passes.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Dominators.h"

#include <bitset>
#include <memory>
#include <string>



using namespace llvm;
using std::string;
using std::unique_ptr;


static cl::OptionCategory futureFunctionsCategory{"future functions options"};

static cl::opt<string> inPath{cl::Positional,
                              cl::desc{"<Module to analyze>"},
                              cl::value_desc{"bitcode filename"},
                              cl::init(""),
                              cl::Required,
                              cl::cat{futureFunctionsCategory}};


class FutureFunctionsPass : public llvm::ModulePass {
public:
  FutureFunctionsPass()
    : llvm::ModulePass{ID}
      { }

  bool runOnModule(llvm::Module& m) override;
  void getAnalysisUsage(llvm::AnalysisUsage &info) const override;
  StringRef getPassName() const override;

//private:
  static char ID;
};
char FutureFunctionsPass::ID = 0;

StringRef
FutureFunctionsPass::getPassName() const {
  return "FutureFunctionsPass";
}

bool
FutureFunctionsPass::runOnModule(llvm::Module& m) {
  auto* mainFunction = m.getFunction("main");
  if (!mainFunction) {
    llvm::report_fatal_error("Unable to find main function.");
  }
  llvm::DenseMap<llvm::Function*, llvm::AAResultsWrapperPass*> fAAs;

  for (auto& f : m) {
    if ( f.isDeclaration()) {
      continue;
    }
    llvm::errs() << "\n Get Dom Tree for " << f.getName() << "\n";
    auto* DT = &getAnalysis<DominatorTreeWrapperPass>(f).getDomTree();
    llvm::errs() << "\n Get AAResultsWrapper for " << f.getName() << "\n";
    auto* AA = &getAnalysis<AAResultsWrapperPass>(f);
    llvm::errs() << "\n Get memSSA for " << f.getName() << "\n";
    auto memSSA = std::make_unique<MemorySSA>(f, &AA->getAAResults(), DT);
  
    fAAs.insert({&f, AA});
    //memSSA->print(llvm::outs());
    //Edges backedges;
    //llvm::FindFunctionBackedges(f, backedges);
    //functionBackEdges.try_emplace(&f, backedges);
  }

  for (auto& f : m) {
    llvm::outs() << "\n At function " << f.getName();
    for (auto& bb : f) {
      std::vector<llvm::LoadInst*> loadInsts;
      std::vector<llvm::StoreInst*> storeInsts;
      for (auto& i : bb) {
        auto* loadi = llvm::dyn_cast<llvm::LoadInst>(&i);
        if (loadi != nullptr) {
          loadInsts.push_back(loadi);
        }
        auto* storei = llvm::dyn_cast<llvm::StoreInst>(&i);
        if (storei != nullptr) {
          storeInsts.push_back(storei);
        }
      }

      llvm::outs() << "\n" << f.getName();
      for (auto* loadi : loadInsts) {
        for (auto* storei : storeInsts) {
          llvm::outs() << "\n " << *loadi;
          llvm::outs() << "\n " << *storei;
          //auto* AA = &getAnalysis<AAResultsWrapperPass>(f).getAAResults();
          auto& AA = fAAs[&f]->getAAResults();
          auto storeMemLoc = llvm::MemoryLocation::get(storei);
          auto  loadMemLoc =  llvm::MemoryLocation::get(loadi);
          auto AAResult = AA.alias(storeMemLoc, loadMemLoc);
          if (AAResult == AliasResult::MustAlias) {
            llvm::outs() << "\n Must Alias \n" ;
          }
        }
      }
    }
  }



  return false;
}

void
FutureFunctionsPass::getAnalysisUsage(llvm::AnalysisUsage &info) const {
  //info.setPreservesAll();
  //info.addRequired<DominatorTreeWrapperPass>();
  info.addRequired<AAResultsWrapperPass>();
  info.addPreserved<AAResultsWrapperPass>();
  //info.addRequired<AliasAnalysis>();
  //info.addRequired<PostDominatorTreeWrapperPass>();
}


static void
instrumentFunctions(llvm::Module& m) {
  llvm::DebugFlag = true;
  legacy::PassManager pm;
  pm.add(createTypeBasedAAWrapperPass());
  pm.add(createGlobalsAAWrapperPass());
  pm.add(createSCEVAAWrapperPass());
  pm.add(createScopedNoAliasAAWrapperPass());
  pm.add(createCFLSteensAAWrapperPass());
  pm.add(new llvm::LoopInfoWrapperPass());
  //pm.add(createPostDomTree());
  //pm.add(new MemorySSAWrapperPass());
  pm.add(new DominatorTreeWrapperPass());
  //pm.add(createBasicAAWrapperPass());
  pm.add(new AAResultsWrapperPass());
  pm.add(new FutureFunctionsPass());
  pm.run(m);
}


int
main(int argc, char** argv) {
  // This boilerplate provides convenient stack traces and clean LLVM exit
  // handling. It also initializes the built in support for convenient
  // command line option handling.
  sys::PrintStackTraceOnErrorSignal(argv[0]);
  llvm::PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj shutdown;
  cl::HideUnrelatedOptions(futureFunctionsCategory);
  cl::ParseCommandLineOptions(argc, argv);

  // Construct an IR file from the filename passed on the command line.
  SMDiagnostic err;
  LLVMContext context;
  unique_ptr<Module> module = parseIRFile(inPath.getValue(), err, context);

  if (!module.get()) {
    errs() << "Error reading bitcode file: " << inPath << "\n";
    err.print(argv[0], errs());
    return -1;
  }

  auto* mainFunction = module->getFunction("main");
  if (!mainFunction) {
    llvm::report_fatal_error("Unable to find main function.");
  }
  
  instrumentFunctions(*module);

  return 0;
}
