/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordClockwiseRelabelBatchSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierBatchedRecordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierNormalizedFallbackCompiledRecordSemantics

/-! # Compiled batched semantics of direct final carriers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierCompiledBatchedRecordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local implicit_reducible]
  directSourceFinalStructuralBaseDecidableEq
attribute [local instance]
  directSourceFinalStructuralBaseDecidableEq

/-- Formatting the compiled normalized carrier routes, relabeling them
clockwise, and expanding them in batches produces the batched semantic records
of the direct carrier clauses. -/
theorem directSourceFinalCarrierCompiledBatchedRecords_eq_semantic
    (symbols : List encoding.Γ) :
    HorizontalRoutedRouteTailRecord.batchedRecords
        (BinaryRouteTailRecordClockwiseRelabel.output
          (directSourceFinalCarrierNormalizedFallbackCompiledRouteTailRecordTokens
            decider symbols)) =
      HorizontalRoutedRouteTailRecord.batchedRecords
        (retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          (directSourceFormula decider symbols)
          (directSourceFinalCarrierStart decider symbols)
          (directSourceFinalCarrierClauses decider symbols)) := by
  rw [directSourceFinalCarrierNormalizedFallbackCompiledRouteTailRecordTokens_eq]
  unfold directSourceFinalCarrierNormalizedFallbackRouteTailRecordTokens
  rw [BinaryRouteTailRecordClockwiseRelabel.batchedRecords_output_batchFormatter_records]
  apply Eq.symm
  exact @directSourceFinalCarrierBatchedSemanticRecords_eq_decodedRecords
    Input encoding language decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
