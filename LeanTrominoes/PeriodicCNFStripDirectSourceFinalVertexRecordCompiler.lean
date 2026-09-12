/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTripleRecordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRetainedElementRecordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestAppender
import LeanTrominoes.TM2ListAppendClosure

/-! # The actual unconditional vertex-record appender for the direct strip reduction -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Concatenate the exact triple prefix and three retained-color blocks. -/
noncomputable def directSparseAffineVertexRequestTokenCompiler :
    TM2ComputableInPolyTime id id (directSparseComputedAffineVertexRequestsOfSymbols decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    let compiler := TM2ListAppend.computableInPolyTime
      (directSourceFinalTripleRecordsComputableInPolyTime decider)
      (TM2ListAppend.computableInPolyTime
        (directSourceFinalRetainedElementRecordsComputableInPolyTime decider .red)
        (TM2ListAppend.computableInPolyTime
          (directSourceFinalRetainedElementRecordsComputableInPolyTime decider .green)
          (directSourceFinalRetainedElementRecordsComputableInPolyTime decider .blue)))
    apply Turing.TM2ComputableInPolyTime.of_eq compiler
    intro symbols
    rw [directSparseComputedAffineVertexRequestsOfSymbols_eq_indexed,
      directSparseComputedAffineIndexedVertexRequestsOfSymbols_eq_blocks,
      directSparseComputedAffineIndexedElementRequestsOfSymbols_eq_table,
      directSparseComputedAffineIndexedElementRequestsOfSymbols_eq_table,
      directSparseComputedAffineIndexedElementRequestsOfSymbols_eq_table]
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

/-- Retain the source word and append its complete compact vertex-request prefix. -/
noncomputable def directSparseAffineVertexRequestAppender :
    DirectSparseAffineVertexRequestAppender decider :=
  RetainedInputAppendPipeline.appendedComputableInPolyTimeOfCompiler
    (directSparseComputedAffineVertexRequestsOfSymbols decider)
    (directSparseAffineVertexRequestTokenCompiler decider)

/-- The vertex appender required by the final closure has no remaining compiler premise. -/
noncomputable def directSparseVertexRecordAppender :
    DirectSparseVertexRecordAppender decider :=
  directSparseVertexRecordAppenderOfAffineRequests decider
    (directSparseAffineVertexRequestAppender decider)

end LeanTrominoes.PeriodicCNFStripReduction
end
