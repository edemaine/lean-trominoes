/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedValueLookupProjectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanDataSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableFanCountPredSemantics
import LeanTrominoes.StableOccurrenceRankCandidateKeyComponents
import LeanTrominoes.StableOccurrenceRankCyclicSuccessorPermutation

/-! # Grouped variable-fan counts recovered from current keys -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The finite count predecessor beside each grouped key is the bounded
predecessor of the multiplicity of the identity recovered by quotient. -/
theorem directSourceFinalGroupedVariableFanCountPreds_eq_map_countPred
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableFanData decider symbols).map
        (fun fan => fan.countPred) =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map fun key =>
        BoundedPositiveCountPreds.boundedPositiveCountPred
          ((directSourceFinalAtomIdentityCodes decider symbols).count
            (key / 3)) := by
  rw [directSourceFinalGroupedVariableFanData_eq_map_alignedDatum]
  have projected :=
    FiniteAlphabetKeyedValueLookup.map_alignedDatum_projection
      (directSourceFinalUniqueFanQueryKeys decider symbols)
      (directSourceFinalOccurrenceCandidateKeys decider symbols)
      (directSourceFinalVariableFanData decider symbols)
      (fun fan => fan.countPred)
      (by rw [directSourceFinalOccurrenceCandidateKeys_length,
        directSourceFinalVariableFanData_length])
      (fun query queryMember =>
        directSourceFinalUniqueFanQueryKey_mem_candidateKeys
          decider symbols query queryMember)
  rw [directSourceFinalVariableFanData_countPreds] at projected
  rw [projected]
  apply List.map_congr_left
  intro query queryMember
  have queryCandidate' : query ∈ StableOccurrenceRanks.candidateKeys
      (directSourceFinalAtomIdentityCodes decider symbols) := by
    rw [← directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
    exact directSourceFinalUniqueFanQueryKey_mem_candidateKeys
      decider symbols query queryMember
  rw [directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys,
    directSourceFinalOccurrenceCountPreds_eq_identityCodes]
  exact StableOccurrenceRanks.alignedCountPred_eq
    (directSourceFinalAtomIdentityCodes decider symbols)
    (fun value _valueMember =>
      directSourceFinalAtomIdentityCodes_count_le_three
        decider symbols value)
    query queryCandidate'

/-- The active count of the fan beside each grouped key is the multiplicity
of the identity recovered by base-three quotient. -/
theorem directSourceFinalGroupedVariableFanCounts_eq_map_count
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableFanData decider symbols).map
        VariableRibbonFanData.count =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map
        fun key =>
          (directSourceFinalAtomIdentityCodes decider symbols).count
            (key / 3) := by
  have projectedCountPreds :
      (directSourceFinalGroupedVariableFanData decider symbols).map
          (fun fan => fan.countPred) =
        (directSourceFinalUniqueFanQueryKeys decider symbols).map
          (FiniteAlphabetKeyedValueLookup.alignedDatum
            (directSourceFinalOccurrenceCandidateKeys decider symbols)
            (directSourceFinalOccurrenceCountPreds decider symbols)) := by
    rw [directSourceFinalGroupedVariableFanData_eq_map_alignedDatum]
    have projected :=
      FiniteAlphabetKeyedValueLookup.map_alignedDatum_projection
        (directSourceFinalUniqueFanQueryKeys decider symbols)
        (directSourceFinalOccurrenceCandidateKeys decider symbols)
        (directSourceFinalVariableFanData decider symbols)
        (fun fan => fan.countPred)
        (by rw [directSourceFinalOccurrenceCandidateKeys_length,
          directSourceFinalVariableFanData_length])
        (fun query queryMember =>
          directSourceFinalUniqueFanQueryKey_mem_candidateKeys
            decider symbols query queryMember)
    rw [directSourceFinalVariableFanData_countPreds] at projected
    exact projected
  have countMap :
      (directSourceFinalGroupedVariableFanData decider symbols).map
          VariableRibbonFanData.count =
        ((directSourceFinalGroupedVariableFanData decider symbols).map
          fun fan => fan.countPred).map
            fun countPred => countPred.val + 1 := by
    rw [List.map_map]
    rfl
  rw [countMap, projectedCountPreds, List.map_map]
  apply List.map_congr_left
  intro query queryMember
  have queryCandidate' : query ∈ StableOccurrenceRanks.candidateKeys
      (directSourceFinalAtomIdentityCodes decider symbols) := by
    rw [← directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
    exact directSourceFinalUniqueFanQueryKey_mem_candidateKeys
      decider symbols query queryMember
  rw [directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys,
    directSourceFinalOccurrenceCountPreds_eq_identityCodes]
  change
    (FiniteAlphabetKeyedValueLookup.alignedDatum
      (StableOccurrenceRanks.candidateKeys
        (directSourceFinalAtomIdentityCodes decider symbols))
      ((directSourceFinalAtomIdentityCodes decider symbols).map fun value =>
        BoundedPositiveCountPreds.boundedPositiveCountPred
          ((directSourceFinalAtomIdentityCodes decider symbols).count value))
      query).val + 1 =
        (directSourceFinalAtomIdentityCodes decider symbols).count
          (query / 3)
  rw [StableOccurrenceRanks.alignedCountPred_eq
      (directSourceFinalAtomIdentityCodes decider symbols)
      (fun value _valueMember =>
        directSourceFinalAtomIdentityCodes_count_le_three
          decider symbols value)
      query queryCandidate']
  apply BoundedPositiveCountPreds.boundedPositiveCountPred_add_one_of_pos_le_three
  · rcases (StableOccurrenceRanks.mem_candidateKeys_iff
      (directSourceFinalAtomIdentityCodes decider symbols) query).mp
        queryCandidate' with
      ⟨value, rank, valueMember, rankLt, queryEq⟩
    have rankThree : rank < 3 := lt_of_lt_of_le rankLt
      (directSourceFinalAtomIdentityCodes_count_le_three
        decider symbols value)
    have valueEq : value = query / 3 := by omega
    rw [← valueEq]
    exact List.count_pos_iff.mpr valueMember
  · exact directSourceFinalAtomIdentityCodes_count_le_three
      decider symbols (query / 3)

end LeanTrominoes.PeriodicCNFStripReduction

end
