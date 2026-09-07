/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FinalFanDataStableProjection
import LeanTrominoes.FinalFanQueryRankKeyMapSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanQueryKeySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableFanDataSemantics

/-! # Stable-key semantics of compiled final variable fans -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The selected occurrence-record stream is the explicit three-rank stable
lookup block of every presented identity. -/
theorem directSourceFinalFanSelectedOccurrenceDataExpected_eq_flatMap
    (symbols : List encoding.Γ) :
    directSourceFinalFanSelectedOccurrenceDataExpected decider symbols =
      (directSourceFinalAtomIdentityCodes decider symbols).flatMap fun value =>
        (FinalFanQueryRanks.block
          (BoundedPositiveCountPreds.boundedPositiveCountPred
            ((directSourceFinalAtomIdentityCodes decider symbols).count
              value))).map fun rank =>
          FiniteAlphabetKeyedValueLookup.alignedDatum
            (directSourceFinalOccurrenceCandidateKeys decider symbols)
            (directSourceFinalVariableOccurrenceData decider symbols)
            (value * 3 + rank.val) := by
  unfold directSourceFinalFanSelectedOccurrenceDataExpected
  rw [directSourceFinalFanQueryKeys_eq_keyedBlocks]
  exact FinalFanQueryRanks.map_keyedBlocks _ _

/-- The repeated count-predecessor column is three copies of the bounded
multiplicity attached to each presented identity. -/
theorem directSourceFinalFanRepeatedCountPreds_eq_flatMap
    (symbols : List encoding.Γ) :
    directSourceFinalFanRepeatedCountPreds decider symbols =
      (directSourceFinalAtomIdentityCodes decider symbols).flatMap fun value =>
        List.replicate 3
          (BoundedPositiveCountPreds.boundedPositiveCountPred
            ((directSourceFinalAtomIdentityCodes decider symbols).count
              value)) := by
  unfold directSourceFinalFanRepeatedCountPreds
  rw [directSourceFinalOccurrenceCountPreds_eq_identityCodes,
    List.flatMap_map]

/-- The compiled fan list is exactly one semantic stable-key fan per
clause-major occurrence. -/
theorem directSourceFinalVariableFanData_eq_map_stableFan
    (symbols : List encoding.Γ) :
    directSourceFinalVariableFanData decider symbols =
      (directSourceFinalAtomIdentityCodes decider symbols).map fun value =>
        FinalFanDataTripleAssembler.stableFan
          (directSourceFinalOccurrenceCandidateKeys decider symbols)
          (directSourceFinalVariableOccurrenceData decider symbols)
          value
          (BoundedPositiveCountPreds.boundedPositiveCountPred
            ((directSourceFinalAtomIdentityCodes decider symbols).count
              value)) := by
  rw [directSourceFinalVariableFanData_eq_expected]
  unfold directSourceFinalVariableFanDataExpected
    directSourceFinalFanSelectedCountedOccurrencesExpected
  rw [directSourceFinalFanSelectedOccurrenceDataExpected_eq_flatMap,
    directSourceFinalFanRepeatedCountPreds_eq_flatMap]
  rw [FinalFanDataTripleAssembler.output_eq_grouped]
  rw [FinalFanDataTripleAssembler.map_zip_stableSelected_replicate]
  exact FinalFanDataTripleAssembler.grouped_flatMap_stableFanPairBlock
    (directSourceFinalOccurrenceCandidateKeys decider symbols)
    (directSourceFinalVariableOccurrenceData decider symbols)
    (fun value =>
      BoundedPositiveCountPreds.boundedPositiveCountPred
        ((directSourceFinalAtomIdentityCodes decider symbols).count value))
    (directSourceFinalAtomIdentityCodes decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
