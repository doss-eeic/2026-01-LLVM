//===- NewPMDriver.cpp - Driver for opt with new PM -----------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
///
/// This file is just a split of the code that logically belongs in opt.cpp but
/// that includes the new pass manager headers.
///
//===----------------------------------------------------------------------===//

#include "NewPMDriver.h"
#include "llvm/ADT/Any.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/RuntimeLibcallInfo.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Bitcode/BitcodeWriterPass.h"
#include "llvm/Analysis/LazyCallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/CodeGen/LibcallLoweringInfo.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRPrinter/IRPrintingPasses.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/StandardInstrumentations.h"
#include "llvm/Plugins/PassPlugin.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/Timer.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/VirtualFileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/IPO/ThinLTOBitcodeWriter.h"
#include "llvm/Transforms/Instrumentation/AddressSanitizer.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/AssignGUID.h"
#include "llvm/Transforms/Utils/Debugify.h"
#include "llvm/Transforms/Utils/ProfileVerify.h"
#include <chrono>
#include <tuple>
#include "llvm/ADT/Hashing.h"
#include "llvm/IR/StructuralHash.h"
#include "llvm/Support/MathExtras.h"
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <vector>

using namespace llvm;

static cl::opt<bool> PrintPassSummary(
    "print-pass-summary",
    cl::desc("Print a one-line summary (instruction/BB counts and per-opcode "
             "changes) for each pass that changed the IR"),
    cl::init(false));

static cl::opt<bool> PrintPassSummaryTime(
    "print-pass-summary-time",
    cl::desc("With -print-pass-summary, also print the elapsed time of each "
             "pass in microseconds"),
    cl::init(false));

static cl::opt<unsigned> PassSummaryMinTimeUs(
    "print-pass-summary-min-time-us",
    cl::desc("With -print-pass-summary-time, also print passes that did not "
             "change the IR if they took at least this many microseconds "
             "(0 = only print passes that changed the IR)"),
    cl::init(0));
using namespace opt_tool;

cl::opt<bool> llvm::DebugifyEach(
    "debugify-each",
    cl::desc("Start each pass with debugify and end it with check-debugify"));

cl::opt<std::string> llvm::DebugifyExport(
    "debugify-export",
    cl::desc("Export per-pass debugify statistics to this file"),
    cl::value_desc("filename"));

cl::opt<bool> llvm::VerifyEachDebugInfoPreserve(
    "verify-each-debuginfo-preserve",
    cl::desc("Start each pass with collecting and end it with checking of "
             "debug info preservation."));

cl::opt<std::string> llvm::VerifyDIPreserveExport(
    "verify-di-preserve-export",
    cl::desc("Export debug info preservation failures into "
             "specified (JSON) file (should be abs path as we use"
             " append mode to insert new JSON objects)"),
    cl::value_desc("filename"), cl::init(""));

static cl::opt<bool> EnableLoopFusion("enable-loopfusion", cl::init(false),
                                      cl::Hidden,
                                      cl::desc("Enable the LoopFuse Pass"));

enum class DebugLogging { None, Normal, Verbose, Quiet };

static cl::opt<DebugLogging> DebugPM(
    "debug-pass-manager", cl::Hidden, cl::ValueOptional,
    cl::desc("Print pass management debugging information"),
    cl::init(DebugLogging::None),
    cl::values(
        clEnumValN(DebugLogging::Normal, "", ""),
        clEnumValN(DebugLogging::Quiet, "quiet",
                   "Skip printing info about analyses"),
        clEnumValN(
            DebugLogging::Verbose, "verbose",
            "Print extra information about adaptors and pass managers")));

// This flag specifies a textual description of the alias analysis pipeline to
// use when querying for aliasing information. It only works in concert with
// the "passes" flag above.
static cl::opt<std::string>
    AAPipeline("aa-pipeline",
               cl::desc("A textual description of the alias analysis "
                        "pipeline for handling managed aliasing queries"),
               cl::Hidden, cl::init("default"));

/// {{@ These options accept textual pipeline descriptions which will be
/// inserted into default pipelines at the respective extension points
static cl::opt<std::string> PeepholeEPPipeline(
    "passes-ep-peephole",
    cl::desc("A textual description of the function pass pipeline inserted at "
             "the Peephole extension points into default pipelines"),
    cl::Hidden);
static cl::opt<std::string> LateLoopOptimizationsEPPipeline(
    "passes-ep-late-loop-optimizations",
    cl::desc(
        "A textual description of the loop pass pipeline inserted at "
        "the LateLoopOptimizations extension point into default pipelines"),
    cl::Hidden);
static cl::opt<std::string> LoopOptimizerEndEPPipeline(
    "passes-ep-loop-optimizer-end",
    cl::desc("A textual description of the loop pass pipeline inserted at "
             "the LoopOptimizerEnd extension point into default pipelines"),
    cl::Hidden);
static cl::opt<std::string> ScalarOptimizerLateEPPipeline(
    "passes-ep-scalar-optimizer-late",
    cl::desc("A textual description of the function pass pipeline inserted at "
             "the ScalarOptimizerLate extension point into default pipelines"),
    cl::Hidden);
static cl::opt<std::string> CGSCCOptimizerLateEPPipeline(
    "passes-ep-cgscc-optimizer-late",
    cl::desc("A textual description of the cgscc pass pipeline inserted at "
             "the CGSCCOptimizerLate extension point into default pipelines"),
    cl::Hidden);
static cl::opt<std::string> VectorizerStartEPPipeline(
    "passes-ep-vectorizer-start",
    cl::desc("A textual description of the function pass pipeline inserted at "
             "the VectorizerStart extension point into default pipelines"),
    cl::Hidden);
static cl::opt<std::string> VectorizerEndEPPipeline(
    "passes-ep-vectorizer-end",
    cl::desc("A textual description of the function pass pipeline inserted at "
             "the VectorizerEnd extension point into default pipelines"),
    cl::Hidden);
static cl::opt<std::string> PipelineStartEPPipeline(
    "passes-ep-pipeline-start",
    cl::desc("A textual description of the module pass pipeline inserted at "
             "the PipelineStart extension point into default pipelines"),
    cl::Hidden);
static cl::opt<std::string> PipelineEarlySimplificationEPPipeline(
    "passes-ep-pipeline-early-simplification",
    cl::desc("A textual description of the module pass pipeline inserted at "
             "the EarlySimplification extension point into default pipelines"),
    cl::Hidden);
static cl::opt<std::string> OptimizerEarlyEPPipeline(
    "passes-ep-optimizer-early",
    cl::desc("A textual description of the module pass pipeline inserted at "
             "the OptimizerEarly extension point into default pipelines"),
    cl::Hidden);
static cl::opt<std::string> OptimizerLastEPPipeline(
    "passes-ep-optimizer-last",
    cl::desc("A textual description of the module pass pipeline inserted at "
             "the OptimizerLast extension point into default pipelines"),
    cl::Hidden);
static cl::opt<std::string> FullLinkTimeOptimizationEarlyEPPipeline(
    "passes-ep-full-link-time-optimization-early",
    cl::desc("A textual description of the module pass pipeline inserted at "
             "the FullLinkTimeOptimizationEarly extension point into default "
             "pipelines"),
    cl::Hidden);
static cl::opt<std::string> FullLinkTimeOptimizationLastEPPipeline(
    "passes-ep-full-link-time-optimization-last",
    cl::desc("A textual description of the module pass pipeline inserted at "
             "the FullLinkTimeOptimizationLast extension point into default "
             "pipelines"),
    cl::Hidden);
static cl::opt<std::string> ThinLinkTimeOptimizationEarlyEPPipeline(
    "passes-ep-thin-link-time-optimization-early",
    cl::desc("A textual description of the module pass pipeline inserted at "
             "the ThinLinkTimeOptimizationEarly extension point into default "
             "pipelines"),
    cl::Hidden);
static cl::opt<std::string> ThinLinkTimeOptimizationLastEPPipeline(
    "passes-ep-thin-link-time-optimization-last",
    cl::desc("A textual description of the module pass pipeline inserted at "
             "the ThinLinkTimeOptimizationLast extension point into default "
             "pipelines"),
    cl::Hidden);
/// @}}

static cl::opt<bool> DisablePipelineVerification(
    "disable-pipeline-verification",
    cl::desc("Only has an effect when specified with -print-pipeline-passes. "
             "Disables verifying that the textual pipeline generated by "
             "-print-pipeline-passes can be used to create a pipeline."),
    cl::Hidden);


static cl::opt<PGOKind>
    PGOKindFlag("pgo-kind", cl::init(NoPGO), cl::Hidden,
                cl::desc("The kind of profile guided optimization"),
                cl::values(clEnumValN(NoPGO, "nopgo", "Do not use PGO."),
                           clEnumValN(InstrGen, "pgo-instr-gen-pipeline",
                                      "Instrument the IR to generate profile."),
                           clEnumValN(InstrUse, "pgo-instr-use-pipeline",
                                      "Use instrumented profile to guide PGO."),
                           clEnumValN(SampleUse, "pgo-sample-use-pipeline",
                                      "Use sampled profile to guide PGO.")));
static cl::opt<std::string> ProfileFile("profile-file",
                                 cl::desc("Path to the profile."), cl::Hidden);
static cl::opt<std::string>
    MemoryProfileFile("memory-profile-file",
                      cl::desc("Path to the memory profile."), cl::Hidden);

static cl::opt<CSPGOKind> CSPGOKindFlag(
    "cspgo-kind", cl::init(NoCSPGO), cl::Hidden,
    cl::desc("The kind of context sensitive profile guided optimization"),
    cl::values(
        clEnumValN(NoCSPGO, "nocspgo", "Do not use CSPGO."),
        clEnumValN(
            CSInstrGen, "cspgo-instr-gen-pipeline",
            "Instrument (context sensitive) the IR to generate profile."),
        clEnumValN(
            CSInstrUse, "cspgo-instr-use-pipeline",
            "Use instrumented (context sensitive) profile to guide PGO.")));

static cl::opt<std::string> CSProfileGenFile(
    "cs-profilegen-file",
    cl::desc("Path to the instrumented context sensitive profile."),
    cl::Hidden);

static cl::opt<std::string>
    ProfileRemappingFile("profile-remapping-file",
                         cl::desc("Path to the profile remapping file."),
                         cl::Hidden);

static cl::opt<PGOOptions::ColdFuncOpt> PGOColdFuncAttr(
    "pgo-cold-func-opt", cl::init(PGOOptions::ColdFuncOpt::Default), cl::Hidden,
    cl::desc(
        "Function attribute to apply to cold functions as determined by PGO"),
    cl::values(clEnumValN(PGOOptions::ColdFuncOpt::Default, "default",
                          "Default (no attribute)"),
               clEnumValN(PGOOptions::ColdFuncOpt::OptSize, "optsize",
                          "Mark cold functions with optsize."),
               clEnumValN(PGOOptions::ColdFuncOpt::MinSize, "minsize",
                          "Mark cold functions with minsize."),
               clEnumValN(PGOOptions::ColdFuncOpt::OptNone, "optnone",
                          "Mark cold functions with optnone.")));

static cl::opt<bool> DebugInfoForProfiling(
    "debug-info-for-profiling", cl::init(false), cl::Hidden,
    cl::desc("Emit special debug info to enable PGO profile generation."));

static cl::opt<bool> PseudoProbeForProfiling(
    "pseudo-probe-for-profiling", cl::init(false), cl::Hidden,
    cl::desc("Emit pseudo probes to enable PGO profile generation."));

static cl::opt<bool> DisableLoopUnrolling(
    "disable-loop-unrolling",
    cl::desc("Disable loop unrolling in all relevant passes"), cl::init(false));

template <typename PassManagerT>
bool tryParsePipelineText(PassBuilder &PB,
                          const cl::opt<std::string> &PipelineOpt) {
  if (PipelineOpt.empty())
    return false;

  // Verify the pipeline is parseable:
  PassManagerT PM;
  if (auto Err = PB.parsePassPipeline(PM, PipelineOpt)) {
    errs() << "Could not parse -" << PipelineOpt.ArgStr
           << " pipeline: " << toString(std::move(Err))
           << "... I'm going to ignore it.\n";
    return false;
  }
  return true;
}

/// If one of the EPPipeline command line options was given, register callbacks
/// for parsing and inserting the given pipeline
static void registerEPCallbacks(PassBuilder &PB) {
  if (tryParsePipelineText<FunctionPassManager>(PB, PeepholeEPPipeline))
    PB.registerPeepholeEPCallback(
        [&PB](FunctionPassManager &PM, OptimizationLevel Level) {
          ExitOnError Err("Unable to parse PeepholeEP pipeline: ");
          Err(PB.parsePassPipeline(PM, PeepholeEPPipeline));
        });
  if (tryParsePipelineText<LoopPassManager>(PB,
                                            LateLoopOptimizationsEPPipeline))
    PB.registerLateLoopOptimizationsEPCallback(
        [&PB](LoopPassManager &PM, OptimizationLevel Level) {
          ExitOnError Err("Unable to parse LateLoopOptimizationsEP pipeline: ");
          Err(PB.parsePassPipeline(PM, LateLoopOptimizationsEPPipeline));
        });
  if (tryParsePipelineText<LoopPassManager>(PB, LoopOptimizerEndEPPipeline))
    PB.registerLoopOptimizerEndEPCallback(
        [&PB](LoopPassManager &PM, OptimizationLevel Level) {
          ExitOnError Err("Unable to parse LoopOptimizerEndEP pipeline: ");
          Err(PB.parsePassPipeline(PM, LoopOptimizerEndEPPipeline));
        });
  if (tryParsePipelineText<FunctionPassManager>(PB,
                                                ScalarOptimizerLateEPPipeline))
    PB.registerScalarOptimizerLateEPCallback(
        [&PB](FunctionPassManager &PM, OptimizationLevel Level) {
          ExitOnError Err("Unable to parse ScalarOptimizerLateEP pipeline: ");
          Err(PB.parsePassPipeline(PM, ScalarOptimizerLateEPPipeline));
        });
  if (tryParsePipelineText<CGSCCPassManager>(PB, CGSCCOptimizerLateEPPipeline))
    PB.registerCGSCCOptimizerLateEPCallback(
        [&PB](CGSCCPassManager &PM, OptimizationLevel Level) {
          ExitOnError Err("Unable to parse CGSCCOptimizerLateEP pipeline: ");
          Err(PB.parsePassPipeline(PM, CGSCCOptimizerLateEPPipeline));
        });
  if (tryParsePipelineText<FunctionPassManager>(PB, VectorizerStartEPPipeline))
    PB.registerVectorizerStartEPCallback(
        [&PB](FunctionPassManager &PM, OptimizationLevel Level) {
          ExitOnError Err("Unable to parse VectorizerStartEP pipeline: ");
          Err(PB.parsePassPipeline(PM, VectorizerStartEPPipeline));
        });
  if (tryParsePipelineText<FunctionPassManager>(PB, VectorizerEndEPPipeline))
    PB.registerVectorizerEndEPCallback(
        [&PB](FunctionPassManager &PM, OptimizationLevel Level) {
          ExitOnError Err("Unable to parse VectorizerEndEP pipeline: ");
          Err(PB.parsePassPipeline(PM, VectorizerEndEPPipeline));
        });
  if (tryParsePipelineText<ModulePassManager>(PB, PipelineStartEPPipeline))
    PB.registerPipelineStartEPCallback(
        [&PB](ModulePassManager &PM, OptimizationLevel) {
          ExitOnError Err("Unable to parse PipelineStartEP pipeline: ");
          Err(PB.parsePassPipeline(PM, PipelineStartEPPipeline));
        });
  if (tryParsePipelineText<ModulePassManager>(
          PB, PipelineEarlySimplificationEPPipeline))
    PB.registerPipelineEarlySimplificationEPCallback(
        [&PB](ModulePassManager &PM, OptimizationLevel, ThinOrFullLTOPhase) {
          ExitOnError Err("Unable to parse EarlySimplification pipeline: ");
          Err(PB.parsePassPipeline(PM, PipelineEarlySimplificationEPPipeline));
        });
  if (tryParsePipelineText<ModulePassManager>(PB, OptimizerEarlyEPPipeline))
    PB.registerOptimizerEarlyEPCallback(
        [&PB](ModulePassManager &PM, OptimizationLevel, ThinOrFullLTOPhase) {
          ExitOnError Err("Unable to parse OptimizerEarlyEP pipeline: ");
          Err(PB.parsePassPipeline(PM, OptimizerEarlyEPPipeline));
        });
  if (tryParsePipelineText<ModulePassManager>(PB, OptimizerLastEPPipeline))
    PB.registerOptimizerLastEPCallback(
        [&PB](ModulePassManager &PM, OptimizationLevel, ThinOrFullLTOPhase) {
          ExitOnError Err("Unable to parse OptimizerLastEP pipeline: ");
          Err(PB.parsePassPipeline(PM, OptimizerLastEPPipeline));
        });
  if (tryParsePipelineText<ModulePassManager>(
          PB, FullLinkTimeOptimizationEarlyEPPipeline))
    PB.registerFullLinkTimeOptimizationEarlyEPCallback(
        [&PB](ModulePassManager &PM, OptimizationLevel) {
          ExitOnError Err(
              "Unable to parse FullLinkTimeOptimizationEarlyEP pipeline: ");
          Err(PB.parsePassPipeline(PM,
                                   FullLinkTimeOptimizationEarlyEPPipeline));
        });
  if (tryParsePipelineText<ModulePassManager>(
          PB, FullLinkTimeOptimizationLastEPPipeline))
    PB.registerFullLinkTimeOptimizationLastEPCallback(
        [&PB](ModulePassManager &PM, OptimizationLevel) {
          ExitOnError Err(
              "Unable to parse FullLinkTimeOptimizationLastEP pipeline: ");
          Err(PB.parsePassPipeline(PM, FullLinkTimeOptimizationLastEPPipeline));
        });
  if (tryParsePipelineText<ModulePassManager>(
          PB, ThinLinkTimeOptimizationEarlyEPPipeline))
    PB.registerThinLinkTimeOptimizationEarlyEPCallback(
        [&PB](ModulePassManager &PM, OptimizationLevel) {
          ExitOnError Err(
              "Unable to parse ThinLinkTimeOptimizationEarlyEP pipeline: ");
          Err(PB.parsePassPipeline(PM,
                                   ThinLinkTimeOptimizationEarlyEPPipeline));
        });
  if (tryParsePipelineText<ModulePassManager>(
          PB, ThinLinkTimeOptimizationLastEPPipeline))
    PB.registerThinLinkTimeOptimizationLastEPCallback(
        [&PB](ModulePassManager &PM, OptimizationLevel) {
          ExitOnError Err(
              "Unable to parse ThinLinkTimeOptimizationLastEP pipeline: ");
          Err(PB.parsePassPipeline(PM, ThinLinkTimeOptimizationLastEPPipeline));
        });
}

namespace {
struct IRStats {
  std::string Name;
  unsigned BBs = 0;
  unsigned Insts = 0;
  std::map<unsigned, unsigned> Ops; // opcode -> count
  // For loops: the parent function, which outlives a deleted loop.
  const Function *Parent = nullptr;
  // Kind of IR unit: module, function, loop or scc.
  const char *Kind = "";
  // Set right after the pre-pass measurement, so that the measurement itself
  // is not included in the pass time.
  std::chrono::steady_clock::time_point Start;
};

// Collect stats for a Module, Function, Loop or CGSCC. Other IR units are
// not handled.
std::optional<IRStats> measureIR(Any IR) {
  IRStats S;
  auto CountBlock = [&S](const BasicBlock &BB) {
    ++S.BBs;
    for (const Instruction &I : BB) {
      ++S.Insts;
      ++S.Ops[I.getOpcode()];
    }
  };
  auto CountFn = [&CountBlock](const Function &F) {
    if (F.isDeclaration())
      return;
    for (const BasicBlock &BB : F)
      CountBlock(BB);
  };

  if (const auto *M = llvm::any_cast<const Module *>(&IR)) {
    S.Name = "[module]";
    S.Kind = "module";
    for (const Function &F : **M)
      CountFn(F);
  } else if (const auto *F = llvm::any_cast<const Function *>(&IR)) {
    S.Name = (*F)->getName().str();
    S.Kind = "function";
    CountFn(**F);
  } else if (const auto *L = llvm::any_cast<const Loop *>(&IR)) {
    const BasicBlock *H = (*L)->getHeader();
    S.Name = "loop %" +
             (H->hasName() ? H->getName().str() : std::string("<unnamed>")) +
             " in " + H->getParent()->getName().str();
    // A loop pass may also change the preheader, exit blocks or guard
    // blocks outside the loop, so measure the whole parent function.
    S.Parent = H->getParent();
    S.Kind = "loop";
    CountFn(*S.Parent);
  } else if (const auto *C =
                 llvm::any_cast<const LazyCallGraph::SCC *>(&IR)) {
    S.Name = "(";
    S.Kind = "scc";
    bool First = true;
    for (const LazyCallGraph::Node &N : **C) {
      if (!First)
        S.Name += ", ";
      First = false;
      S.Name += N.getFunction().getName().str();
      CountFn(N.getFunction());
    }
    S.Name += ")";
  } else {
    return std::nullopt;
  }
  return S;
}

// Skip pass managers and adaptors; they only wrap other passes.
bool isContainerPass(StringRef P) {
  return P.contains("PassManager") || P.contains("Adaptor") ||
         P.contains("AnalysisManagerProxy") || P.contains("RepeatedPass") ||
         P.contains("InlinerWrapper");
}

// Describe per-opcode changes, e.g. "mul -1, shl +1". Empty if unchanged.
std::string describeOpcodeDiff(const IRStats &B, const IRStats &A) {
  std::map<unsigned, int> Delta;
  for (const auto &KV : B.Ops)
    Delta[KV.first] -= static_cast<int>(KV.second);
  for (const auto &KV : A.Ops)
    Delta[KV.first] += static_cast<int>(KV.second);
  std::string Out;
  raw_string_ostream OS(Out);
  bool First = true;
  for (const auto &KV : Delta) {
    if (KV.second == 0)
      continue;
    if (!First)
      OS << ", ";
    First = false;
    OS << Instruction::getOpcodeName(KV.first) << " "
       << (KV.second > 0 ? "+" : "") << KV.second;
  }
  return OS.str();
}
} // namespace

static void printPassSummary(StringRef P, const IRStats &Before,
                             const IRStats &After, int64_t TimeUs) {
  std::string Diff = describeOpcodeDiff(Before, After);
  bool Changed = !(Diff.empty() && Before.BBs == After.BBs);
  // Unchanged passes are normally skipped. With a minimum time they are still
  // shown when they were slow.
  bool Slow = PrintPassSummaryTime && PassSummaryMinTimeUs > 0 &&
              TimeUs >= static_cast<int64_t>(PassSummaryMinTimeUs);
  if (!Changed && !Slow)
    return;
  errs() << "[pass-summary] " << P << " on " << After.Name << ": insts "
         << Before.Insts << " -> " << After.Insts << ", BBs " << Before.BBs
         << " -> " << After.BBs;
  if (!Diff.empty())
    errs() << " | " << Diff;
  if (PrintPassSummaryTime)
    errs() << " | time=" << TimeUs << "us";
  errs() << "\n";
}

static void registerPassSummary(PassInstrumentationCallbacks &PIC) {
  // Passes are nested, so keep the pre-pass stats on a stack.
  auto Stack = std::make_shared<std::vector<std::optional<IRStats>>>();

  PIC.registerBeforeNonSkippedPassCallback([Stack](StringRef P, Any IR) {
    if (isContainerPass(P))
      return;
    std::optional<IRStats> S = measureIR(IR);
    if (S)
      S->Start = std::chrono::steady_clock::now();
    Stack->push_back(std::move(S));
  });

  PIC.registerAfterPassCallback(
      [Stack](StringRef P, Any IR, const PreservedAnalyses &) {
        if (isContainerPass(P) || Stack->empty())
          return;
        auto End = std::chrono::steady_clock::now(); // before measuring
        std::optional<IRStats> Before = std::move(Stack->back());
        Stack->pop_back();
        std::optional<IRStats> After = measureIR(IR);
        if (!Before || !After)
          return;
        int64_t TimeUs = std::chrono::duration_cast<std::chrono::microseconds>(
                             End - Before->Start)
                             .count();
        printPassSummary(P, *Before, *After, TimeUs);
      });

  // If the IR is invalidated (e.g. a deleted loop), the after-pass callback
  // is not run. Pop the stack to keep it in sync, and for loops re-measure
  // the parent function, which still exists. Other units are not recorded.
  PIC.registerAfterPassInvalidatedCallback(
      [Stack](StringRef P, const PreservedAnalyses &) {
        if (isContainerPass(P) || Stack->empty())
          return;
        auto End = std::chrono::steady_clock::now(); // before measuring
        std::optional<IRStats> Before = std::move(Stack->back());
        Stack->pop_back();
        if (!Before || !Before->Parent)
          return;
        std::optional<IRStats> After = measureIR(Any(Before->Parent));
        if (!After)
          return;
        After->Name = Before->Name;
        int64_t TimeUs = std::chrono::duration_cast<std::chrono::microseconds>(
                             End - Before->Start)
                             .count();
        printPassSummary(P, *Before, *After, TimeUs);
      });
}

static cl::opt<bool> PrintPassStats(
    "print-pass-stats",
    cl::desc("Aggregate per pass, IR unit kind and function size band how "
             "often the IR changed and how long the pass took. Print a CSV "
             "table to stderr when the pipeline finishes"),
    cl::init(false));

static cl::opt<bool> PassStatsTextHash(
    "pass-stats-text-hash",
    cl::desc("With -print-pass-stats, also decide whether the IR changed by a "
             "detailed structural hash and by a hash of the printed IR text. "
             "This is slow and meant for measuring how much the cheaper "
             "opcode-count check misses"),
    cl::init(false));

namespace {
struct PassStatsRow {
  uint64_t Runs = 0;
  uint64_t Changed = 0;               // opcode counts or BB count differ
  uint64_t AllPreserved = 0;          // pass reported all analyses preserved
  uint64_t UnchangedNotPreserved = 0; // looks unchanged, but pass says changed
  uint64_t Invalidated = 0;           // IR unit was deleted by the pass
  uint64_t TimeUs = 0;
  uint64_t UnchangedTimeUs = 0;
  // Only filled with -pass-stats-text-hash.
  uint64_t HashedRuns = 0;
  uint64_t ChangedDetail = 0;  // detailed structural hash differs
  uint64_t ChangedText = 0;    // printed IR text differs
  uint64_t TextOnly = 0;       // text differs, opcode check says unchanged
  uint64_t DetailOnly = 0;     // detail hash differs, opcode check unchanged
  uint64_t TextNotDetail = 0;  // text differs, detailed hash does not
  uint64_t UnchangedTextTimeUs = 0;
};
using PassStatsKey = std::tuple<std::string, std::string, unsigned>;

std::map<PassStatsKey, PassStatsRow> &passStatsTable() {
  static std::map<PassStatsKey, PassStatsRow> T;
  return T;
}

// Band 0 is an empty unit; band b >= 1 holds sizes in [2^(b-1), 2^b - 1].
unsigned sizeBand(unsigned Insts) { return Insts ? Log2_32(Insts) + 1 : 0; }

struct UnitHashes {
  uint64_t Detail = 0;
  uint64_t Text = 0;
  bool Valid = false;
};

// Hash one IR unit. Loops use the parent function, like measureIR does.
UnitHashes hashUnit(Any IR) {
  UnitHashes H;
  auto TextOf = [](auto &Obj) {
    std::string Buf;
    raw_string_ostream OS(Buf);
    Obj.print(OS);
    OS.flush();
    return static_cast<uint64_t>(hash_value(StringRef(Buf)));
  };
  if (const auto *M = llvm::any_cast<const Module *>(&IR)) {
    H.Detail = StructuralHash(**M, /*DetailedHash=*/true);
    std::string Buf;
    raw_string_ostream OS(Buf);
    (*M)->print(OS, nullptr);
    OS.flush();
    H.Text = static_cast<uint64_t>(hash_value(StringRef(Buf)));
    H.Valid = true;
  } else if (const auto *F = llvm::any_cast<const Function *>(&IR)) {
    H.Detail = StructuralHash(**F, /*DetailedHash=*/true);
    H.Text = TextOf(**F);
    H.Valid = true;
  } else if (const auto *L = llvm::any_cast<const Loop *>(&IR)) {
    const Function &PF = *(*L)->getHeader()->getParent();
    H.Detail = StructuralHash(PF, /*DetailedHash=*/true);
    H.Text = TextOf(PF);
    H.Valid = true;
  } else if (const auto *C = llvm::any_cast<const LazyCallGraph::SCC *>(&IR)) {
    uint64_t D = 0, T = 0;
    for (const LazyCallGraph::Node &N : **C) {
      const Function &F = N.getFunction();
      D = static_cast<uint64_t>(
          hash_combine(D, (uint64_t)StructuralHash(F, /*DetailedHash=*/true)));
      T = static_cast<uint64_t>(hash_combine(D == 0 ? 0 : T, TextOf(F)));
    }
    H.Detail = D;
    H.Text = T;
    H.Valid = true;
  }
  return H;
}

struct PassStatsFrame {
  std::optional<IRStats> S;
  UnitHashes H;
};

void recordPassStat(StringRef P, const IRStats &Before, bool Changed,
                    bool Preserved, bool Invalidated, int64_t TimeUs,
                    const UnitHashes *HB, const UnitHashes *HA) {
  PassStatsRow &R = passStatsTable()[PassStatsKey(
      P.str(), std::string(Before.Kind), sizeBand(Before.Insts))];
  ++R.Runs;
  R.TimeUs += TimeUs;
  if (Changed)
    ++R.Changed;
  else
    R.UnchangedTimeUs += TimeUs;
  if (Preserved)
    ++R.AllPreserved;
  if (!Changed && !Preserved && !Invalidated)
    ++R.UnchangedNotPreserved;
  if (Invalidated)
    ++R.Invalidated;
  if (!PassStatsTextHash)
    return;
  if (Invalidated) {
    // The unit is gone; count it as changed under every check.
    ++R.HashedRuns;
    ++R.ChangedDetail;
    ++R.ChangedText;
    return;
  }
  if (!HB || !HA || !HB->Valid || !HA->Valid)
    return;
  ++R.HashedRuns;
  bool CD = HB->Detail != HA->Detail;
  bool CT = HB->Text != HA->Text;
  if (CD)
    ++R.ChangedDetail;
  if (CT)
    ++R.ChangedText;
  else
    R.UnchangedTextTimeUs += TimeUs;
  if (CT && !Changed)
    ++R.TextOnly;
  if (CD && !Changed)
    ++R.DetailOnly;
  if (CT && !CD)
    ++R.TextNotDetail;
}

void printPassStatsTable() {
  errs() << "pass-stats,pass,unit,band_min_insts,runs,changed,all_preserved,"
            "unchanged_not_preserved,invalidated,time_us,unchanged_time_us,"
            "hashed_runs,changed_detail,changed_text,text_only,detail_only,"
            "text_not_detail,unchanged_text_time_us\n";
  for (const auto &KV : passStatsTable()) {
    const PassStatsRow &R = KV.second;
    unsigned Band = std::get<2>(KV.first);
    errs() << "pass-stats,\"" << std::get<0>(KV.first) << "\","
           << std::get<1>(KV.first) << "," << (Band ? (1u << (Band - 1)) : 0u)
           << "," << R.Runs << "," << R.Changed << "," << R.AllPreserved << ","
           << R.UnchangedNotPreserved << "," << R.Invalidated << ","
           << R.TimeUs << "," << R.UnchangedTimeUs << "," << R.HashedRuns
           << "," << R.ChangedDetail << "," << R.ChangedText << ","
           << R.TextOnly << "," << R.DetailOnly << "," << R.TextNotDetail << ","
           << R.UnchangedTextTimeUs << "\n";
  }
}

// Prints the table when runPassPipeline returns, whichever way it returns.
struct PassStatsPrinter {
  ~PassStatsPrinter() {
    if (PrintPassStats)
      printPassStatsTable();
  }
};
} // namespace

static void registerPassStats(PassInstrumentationCallbacks &PIC) {
  auto Stack = std::make_shared<std::vector<PassStatsFrame>>();

  PIC.registerBeforeNonSkippedPassCallback([Stack](StringRef P, Any IR) {
    if (isContainerPass(P))
      return;
    PassStatsFrame Fr;
    Fr.S = measureIR(IR);
    if (Fr.S) {
      if (PassStatsTextHash)
        Fr.H = hashUnit(IR);
      // Start the clock after all measuring is done.
      Fr.S->Start = std::chrono::steady_clock::now();
    }
    Stack->push_back(std::move(Fr));
  });

  PIC.registerAfterPassCallback(
      [Stack](StringRef P, Any IR, const PreservedAnalyses &PA) {
        if (isContainerPass(P) || Stack->empty())
          return;
        auto End = std::chrono::steady_clock::now(); // before measuring
        PassStatsFrame Fr = std::move(Stack->back());
        Stack->pop_back();
        if (!Fr.S)
          return;
        std::optional<IRStats> After = measureIR(IR);
        if (!After)
          return;
        UnitHashes HA;
        if (PassStatsTextHash)
          HA = hashUnit(IR);
        int64_t TimeUs = std::chrono::duration_cast<std::chrono::microseconds>(
                             End - Fr.S->Start)
                             .count();
        bool Changed =
            !(Fr.S->Ops == After->Ops && Fr.S->BBs == After->BBs);
        recordPassStat(P, *Fr.S, Changed, PA.areAllPreserved(),
                       /*Invalidated=*/false, TimeUs, &Fr.H, &HA);
      });

  // The unit was invalidated (e.g. a deleted loop). It cannot be measured
  // again, so count the run as changed and as invalidated.
  PIC.registerAfterPassInvalidatedCallback(
      [Stack](StringRef P, const PreservedAnalyses &) {
        if (isContainerPass(P) || Stack->empty())
          return;
        auto End = std::chrono::steady_clock::now();
        PassStatsFrame Fr = std::move(Stack->back());
        Stack->pop_back();
        if (!Fr.S)
          return;
        int64_t TimeUs = std::chrono::duration_cast<std::chrono::microseconds>(
                             End - Fr.S->Start)
                             .count();
        recordPassStat(P, *Fr.S, /*Changed=*/true, /*Preserved=*/false,
                       /*Invalidated=*/true, TimeUs, nullptr, nullptr);
      });
}

bool llvm::runPassPipeline(
    StringRef Arg0, Module &M, TargetMachine *TM, TargetLibraryInfoImpl *TLII,
    ToolOutputFile *Out, ToolOutputFile *ThinLTOLinkOut,
    ToolOutputFile *OptRemarkFile, StringRef PassPipeline,
    ArrayRef<PassPluginLibraryInfo> Extensions,
    ArrayRef<std::function<void(PassBuilder &)>> PassBuilderCallbacks,
    OutputKind OK, VerifierKind VK, bool ShouldPreserveAssemblyUseListOrder,
    bool ShouldPreserveBitcodeUseListOrder, bool EmitSummaryIndex,
    bool EmitModuleHash, bool EnableDebugify, bool VerifyDIPreserve,
    bool EnableProfcheck, bool UnifiedLTO) {
  std::optional<PGOOptions> P;
  switch (PGOKindFlag) {
  case InstrGen:
    P = PGOOptions(ProfileFile, "", "", MemoryProfileFile, PGOOptions::IRInstr,
                   PGOOptions::NoCSAction, PGOColdFuncAttr);
    break;
  case InstrUse:
    P = PGOOptions(ProfileFile, "", ProfileRemappingFile, MemoryProfileFile,
                   PGOOptions::IRUse, PGOOptions::NoCSAction, PGOColdFuncAttr);
    break;
  case SampleUse:
    P = PGOOptions(ProfileFile, "", ProfileRemappingFile, MemoryProfileFile,
                   PGOOptions::SampleUse, PGOOptions::NoCSAction,
                   PGOColdFuncAttr);
    break;
  case NoPGO:
    if (DebugInfoForProfiling || PseudoProbeForProfiling ||
        !MemoryProfileFile.empty())
      P = PGOOptions("", "", "", MemoryProfileFile, PGOOptions::NoAction,
                     PGOOptions::NoCSAction, PGOColdFuncAttr,
                     DebugInfoForProfiling, PseudoProbeForProfiling);
    else
      P = std::nullopt;
  }
  if (CSPGOKindFlag != NoCSPGO) {
    if (P && (P->Action == PGOOptions::IRInstr ||
              P->Action == PGOOptions::SampleUse)) {
      errs() << "CSPGOKind cannot be used with IRInstr or SampleUse";
      return false;
    }
    if (CSPGOKindFlag == CSInstrGen) {
      if (CSProfileGenFile.empty()) {
        errs() << "CSInstrGen needs to specify CSProfileGenFile";
        return false;
      }
      if (P) {
        P->CSAction = PGOOptions::CSIRInstr;
        P->CSProfileGenFile = CSProfileGenFile;
      } else
        P = PGOOptions("", CSProfileGenFile, ProfileRemappingFile,
                       /*MemoryProfile=*/"", PGOOptions::NoAction,
                       PGOOptions::CSIRInstr);
    } else /* CSPGOKindFlag == CSInstrUse */ {
      if (!P) {
        errs() << "CSInstrUse needs to be together with InstrUse";
        return false;
      }
      P->CSAction = PGOOptions::CSIRUse;
    }
  }

  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;

  if (TM) {
    TM->setPGOOption(P);

    MAM.registerPass([&] {
      const TargetOptions &Options = TM->Options;
      return RuntimeLibraryAnalysis(Options.MCOptions.ABIName, Options.VecLib);
    });
  }

  PassInstrumentationCallbacks PIC;
  PrintPassOptions PrintPassOpts;
  PrintPassOpts.Verbose = DebugPM == DebugLogging::Verbose;
  PrintPassOpts.SkipAnalyses = DebugPM == DebugLogging::Quiet;
  StandardInstrumentations SI(M.getContext(), DebugPM != DebugLogging::None,
                              VK == VerifierKind::EachPass, PrintPassOpts);
  SI.registerCallbacks(PIC, &MAM);
  if (PrintPassSummary)
    registerPassSummary(PIC);
  if (PrintPassStats)
    registerPassStats(PIC);
  PassStatsPrinter StatsPrinterGuard;
  DebugifyEachInstrumentation Debugify;
  DebugifyStatsMap DIStatsMap;
  DebugInfoPerPass DebugInfoBeforePass;
  if (DebugifyEach) {
    Debugify.setDIStatsMap(DIStatsMap);
    Debugify.setDebugifyMode(DebugifyMode::SyntheticDebugInfo);
    Debugify.registerCallbacks(PIC, MAM);
  } else if (VerifyEachDebugInfoPreserve) {
    Debugify.setDebugInfoBeforePass(DebugInfoBeforePass);
    Debugify.setDebugifyMode(DebugifyMode::OriginalDebugInfo);
    Debugify.setOrigDIVerifyBugsReportFilePath(
      VerifyDIPreserveExport);
    Debugify.registerCallbacks(PIC, MAM);
  }

  PipelineTuningOptions PTO;
  // LoopUnrolling defaults on to true and DisableLoopUnrolling is initialized
  // to false above so we shouldn't necessarily need to check whether or not the
  // option has been enabled.
  PTO.LoopUnrolling = !DisableLoopUnrolling;
  PTO.UnifiedLTO = UnifiedLTO;
  PTO.LoopFusion = EnableLoopFusion;
  PassBuilder PB(TM, PTO, P, &PIC);
  registerEPCallbacks(PB);

  // Let plugins and linked extensions register pass builder callbacks.
  for (const PassPluginLibraryInfo &Info : Extensions)
    if (Info.RegisterPassBuilderCallbacks)
      Info.RegisterPassBuilderCallbacks(PB);

  // Load any explicitly specified plugins.
  for (auto &PassCallback : PassBuilderCallbacks)
    PassCallback(PB);

  // Specially handle the alias analysis manager so that we can register
  // a custom pipeline of AA passes with it.
  AAManager AA;
  if (auto Err = PB.parseAAPipeline(AA, AAPipeline)) {
    errs() << Arg0 << ": " << toString(std::move(Err)) << "\n";
    return false;
  }

  // Register the AA manager first so that our version is the one used.
  FAM.registerPass([&] { return std::move(AA); });
  // Register our TargetLibraryInfoImpl.
  FAM.registerPass([&] { return TargetLibraryAnalysis(*TLII); });

  // Register all the basic analyses with the managers.
  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  ModulePassManager MPM;
  if (EnableDebugify)
    MPM.addPass(NewPMDebugifyPass());
  if (VerifyDIPreserve)
    MPM.addPass(NewPMDebugifyPass(DebugifyMode::OriginalDebugInfo, "",
                                  &DebugInfoBeforePass));
  if (EnableProfcheck)
    MPM.addPass(createModuleToFunctionPassAdaptor(ProfileInjectorPass()));
  // Add passes according to the -passes options.
  if (!PassPipeline.empty()) {
    if (auto Err = PB.parsePassPipeline(MPM, PassPipeline)) {
      errs() << Arg0 << ": " << toString(std::move(Err)) << "\n";
      return false;
    }
  }

  if (VK != VerifierKind::None)
    MPM.addPass(VerifierPass());
  if (EnableDebugify)
    MPM.addPass(NewPMCheckDebugifyPass(false, "", &DIStatsMap));
  if (VerifyDIPreserve)
    MPM.addPass(NewPMCheckDebugifyPass(
        false, "", nullptr, DebugifyMode::OriginalDebugInfo,
        &DebugInfoBeforePass, VerifyDIPreserveExport));
  if (EnableProfcheck)
    MPM.addPass(ProfileVerifierPass());

  // Add any relevant output pass at the end of the pipeline.
  switch (OK) {
  case OK_NoOutput:
    break; // No output pass needed.
  case OK_OutputAssembly:
    if (EmitSummaryIndex) {
      MPM.addPass(AssignGUIDPass());
    }
    MPM.addPass(PrintModulePass(
        Out->os(), "", ShouldPreserveAssemblyUseListOrder, EmitSummaryIndex,
        /*ShouldRenumberMetadata=*/true));
    break;
  case OK_OutputBitcode:
    if (EmitSummaryIndex) {
      MPM.addPass(AssignGUIDPass());
    }
    MPM.addPass(BitcodeWriterPass(Out->os(), ShouldPreserveBitcodeUseListOrder,
                                  EmitSummaryIndex, EmitModuleHash));
    break;
  case OK_OutputThinLTOBitcode:
    MPM.addPass(AssignGUIDPass());
    MPM.addPass(ThinLTOBitcodeWriterPass(
        Out->os(), ThinLTOLinkOut ? &ThinLTOLinkOut->os() : nullptr,
        ShouldPreserveBitcodeUseListOrder));
    break;
  }

  // Before executing passes, print the final values of the LLVM options.
  cl::PrintOptionValues();

  // Print a textual, '-passes=' compatible, representation of pipeline if
  // requested.
  if (std::optional<PrintPipelinePassesFormat> Format =
          PB.getPrintPipelinePasses()) {
    std::string Pipeline;
    raw_string_ostream SOS(Pipeline);
    MPM.printPipeline(SOS, [&PIC](StringRef ClassName) {
      auto PassName = PIC.getPassNameForClassName(ClassName);
      return PassName.empty() ? ClassName : PassName;
    });
    printFormattedPipelinePasses(outs(), Pipeline, *Format);
    outs() << "\n";

    if (!DisablePipelineVerification) {
      // Check that we can parse the returned pipeline string as an actual
      // pipeline.
      ModulePassManager TempPM;
      if (auto Err = PB.parsePassPipeline(TempPM, Pipeline)) {
        errs() << "Could not parse dumped pass pipeline: "
               << toString(std::move(Err)) << "\n";
        return false;
      }
    }

    return true;
  }

  // Now that we have all of the passes ready, run them.
  MPM.run(M, MAM);

  // If a pass reported an error via LLVMContext::emitError, fail without
  // writing the output module.
  if (auto *DH = M.getContext().getDiagHandlerPtr()) {
    if (DH->HasErrors)
      return false;
  }

  // Declare success.
  if (OK != OK_NoOutput) {
    Out->keep();
    if (OK == OK_OutputThinLTOBitcode && ThinLTOLinkOut)
      ThinLTOLinkOut->keep();
  }

  if (OptRemarkFile)
    OptRemarkFile->keep();

  if (DebugifyEach && !DebugifyExport.empty())
    exportDebugifyStats(DebugifyExport, Debugify.getDebugifyStatsMap());

  TimerGroup::printAll(*CreateInfoOutputFile());
  TimerGroup::clearAll();

  return true;
}

void llvm::printPasses(raw_ostream &OS) {
  PassBuilder PB;
  PB.printPassNames(OS);
}
