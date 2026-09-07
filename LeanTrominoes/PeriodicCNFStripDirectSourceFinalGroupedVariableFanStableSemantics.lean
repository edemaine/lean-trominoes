/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanDataSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableFanStableSemantics
import LeanTrominoes.StableOccurrenceRankCandidateKeyComponents

/-! # Stable-key semantics of grouped final variable fans -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The complete fan beside a grouped occurrence key is the semantic fan of
the key's identity quotient and bounded identity multiplicity. -/
theorem directSourceFinalGroupedVariableFanData_eq_map_stableFan
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableFanData decider symbols =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map fun key =>
        FinalFanDataTripleAssembler.stableFan
          (directSourceFinalOccurrenceCandidateKeys decider symbols)
          (directSourceFinalVariableOccurrenceData decider symbols)
          (key / 3)
          (BoundedPositiveCountPreds.boundedPositiveCountPred
            ((directSourceFinalAtomIdentityCodes decider symbols).count
              (key / 3))) := by
  rw [directSourceFinalGroupedVariableFanData_eq_map_alignedDatum,
    directSourceFinalVariableFanData_eq_map_stableFan]
  apply List.map_congr_left
  intro key keyMember
  have candidateMember : key ∈
      directSourceFinalOccurrenceCandidateKeys decider symbols :=
    directSourceFinalUniqueFanQueryKey_mem_candidateKeys
      decider symbols key keyMember
  have candidateMember' : key ∈ StableOccurrenceRanks.candidateKeys
      (directSourceFinalAtomIdentityCodes decider symbols) := by
    rw [← directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
    exact candidateMember
  have components := StableOccurrenceRanks.candidateKey_getD_components
    (directSourceFinalAtomIdentityCodes decider symbols)
    (fun value _valueMember =>
      directSourceFinalAtomIdentityCodes_count_le_three
        decider symbols value)
    key candidateMember'
  have indexLt :
      (StableOccurrenceRanks.candidateKeys
        (directSourceFinalAtomIdentityCodes decider symbols)).idxOf key <
        (directSourceFinalAtomIdentityCodes decider symbols).length := by
    rw [← StableOccurrenceRanks.candidateKeys_length]
    exact List.idxOf_lt_length_iff.mpr candidateMember'
  rw [directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
  unfold FiniteAlphabetKeyedValueLookup.alignedDatum
  rw [List.getD_eq_getElem _ _ (by simpa using indexLt),
    List.getElem_map]
  have valueEq := components.1
  rw [List.getD_eq_getElem _ _ indexLt] at valueEq
  rw [valueEq]

end LeanTrominoes.PeriodicCNFStripReduction

end
