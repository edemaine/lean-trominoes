/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FinalFanDataTripleAssemblerCountPredSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableFanDataSemantics

/-! # Count predecessors of complete direct final variable fans -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The count-predecessor field of every assembled fan is exactly the
occurrence multiplicity compiled for that fan. -/
theorem directSourceFinalVariableFanData_countPreds
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableFanData decider symbols).map
        (fun fan => fan.countPred) =
      directSourceFinalOccurrenceCountPreds decider symbols := by
  rw [directSourceFinalVariableFanData_eq_expected]
  have lengthEq :
      (directSourceFinalFanSelectedOccurrenceDataExpected
        decider symbols).length =
        3 * (directSourceFinalOccurrenceCountPreds
          decider symbols).length := by
    unfold directSourceFinalFanSelectedOccurrenceDataExpected
    simp
  unfold directSourceFinalVariableFanDataExpected
    directSourceFinalFanSelectedCountedOccurrencesExpected
    directSourceFinalFanRepeatedCountPreds
  change
    (FinalFanDataTripleAssembler.output
      (FinalFanDataTripleAssembler.countedOccurrencePairs
        (directSourceFinalFanSelectedOccurrenceDataExpected decider symbols)
        (directSourceFinalOccurrenceCountPreds decider symbols))).map
          (fun fan => fan.countPred) =
      directSourceFinalOccurrenceCountPreds decider symbols
  exact FinalFanDataTripleAssembler.output_countPreds_countedOccurrencePairs
    (directSourceFinalOccurrenceCountPreds decider symbols)
    (directSourceFinalFanSelectedOccurrenceDataExpected decider symbols)
    lengthEq

end LeanTrominoes.PeriodicCNFStripReduction

end
