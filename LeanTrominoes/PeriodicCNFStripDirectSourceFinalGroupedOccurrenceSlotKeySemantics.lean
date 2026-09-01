/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceSlotSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceKeySemantics
import LeanTrominoes.StableOccurrenceRankCandidateKeyComponents

/-! # Grouped occurrence slots recovered from current keys -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The finite slot beside each grouped current key is exactly its base-three
remainder. -/
theorem directSourceFinalGroupedOccurrenceSlots_eq_map_mod
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedOccurrenceSlots decider symbols =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map
        fun key => BoundedOccurrenceSlots.boundedOccurrenceSlot (key % 3) := by
  rw [directSourceFinalGroupedOccurrenceSlots_eq_map_alignedDatum]
  apply List.map_congr_left
  intro query queryMember
  have queryCandidate : query ∈
      directSourceFinalOccurrenceCandidateKeys decider symbols :=
    directSourceFinalUniqueFanQueryKey_mem_candidateKeys
      decider symbols query queryMember
  have queryCandidate' : query ∈ StableOccurrenceRanks.candidateKeys
      (directSourceFinalAtomIdentityCodes decider symbols) := by
    rw [← directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
    exact queryCandidate
  have components :=
    StableOccurrenceRanks.candidateKey_getD_components
      (directSourceFinalAtomIdentityCodes decider symbols)
      (fun value _valueMember =>
        directSourceFinalAtomIdentityCodes_count_le_three
          decider symbols value)
      query queryCandidate'
  have indexLt :
      (StableOccurrenceRanks.candidateKeys
        (directSourceFinalAtomIdentityCodes decider symbols)).idxOf query <
        (StableOccurrenceRanks.ranks
          (directSourceFinalAtomIdentityCodes decider symbols)).length := by
    rw [StableOccurrenceRanks.ranks_length,
      ← StableOccurrenceRanks.candidateKeys_length]
    exact List.idxOf_lt_length_iff.mpr queryCandidate'
  unfold FiniteAlphabetKeyedValueLookup.alignedDatum
    directSourceFinalOccurrenceSlots BoundedOccurrenceSlots.slots
  rw [directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys,
    directSourceFinalOccurrenceStableRanks_eq_identityCodes]
  rw [List.getD_eq_getElem _ _ (by simpa using indexLt),
    List.getElem_map]
  have rankEq := components.2
  rw [List.getD_eq_getElem _ _ indexLt] at rankEq
  rw [rankEq]

end LeanTrominoes.PeriodicCNFStripReduction

end
