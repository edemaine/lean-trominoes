/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSparseAssignmentRecordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseComputedRecordAppenderCompiler

/-! # Semantic direct sparse record emission from split appenders -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The composed proof-free machine meets the semantic canonical-record
boundary used by the fixed sparse-assignment expander. -/
def directSparseRecordEmitterOfAppenders
    (vertices : DirectSparseVertexRecordAppender decider)
    (routes : DirectSparseRouteRecordAppender decider) :
    TM2ComputableInPolyTime id id
      (directSparseAssignmentRecordsOfSymbols decider) := by
  exact RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directSparseComputedAssignmentRecordsOfSymbols decider)
    (directSparseAssignmentRecordsOfSymbols decider)
    (directSparseComputedAssignmentRecordsOfSymbols_eq decider)
    (directSparseComputedRecordEmitterOfAppenders
      decider vertices routes)

end PeriodicCNFStripReduction
end LeanTrominoes
