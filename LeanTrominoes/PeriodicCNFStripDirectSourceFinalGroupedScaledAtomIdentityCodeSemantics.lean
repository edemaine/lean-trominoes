/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListRangeGetDIndex
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedNextOccurrenceKeyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceIndexSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceKeySemantics
import LeanTrominoes.StableOccurrenceRankCandidateKeyComponents
import LeanTrominoes.UnaryIndexedValueLookupSemantics

/-! # Semantics of regrouped scaled atom identities -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Indexing the clause-major identity bases by the recovered occurrence
positions is the same as keyed lookup beside the grouped current keys. -/
theorem directSourceFinalGroupedScaledAtomIdentityCodes_eq_map_alignedDatum
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedScaledAtomIdentityCodes decider symbols =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map
        (UnaryKeyedValueLookup.alignedDatum
          (directSourceFinalOccurrenceCandidateKeys decider symbols)
          (directSourceFinalScaledAtomIdentityCodes decider symbols)) := by
  unfold directSourceFinalGroupedScaledAtomIdentityCodes
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt]
  · rw [directSourceFinalGroupedOccurrenceIndices_eq_map_alignedDatum,
      List.map_map]
    apply List.map_congr_left
    intro query queryMember
    have queryCandidate : query ∈
        directSourceFinalOccurrenceCandidateKeys decider symbols :=
      directSourceFinalUniqueFanQueryKey_mem_candidateKeys
        decider symbols query queryMember
    have queryIndexLt :
        (directSourceFinalOccurrenceCandidateKeys
          decider symbols).idxOf query <
          (directSourceFinalOccurrenceCandidateKeys
            decider symbols).length :=
      List.idxOf_lt_length_iff.mpr queryCandidate
    unfold UnaryKeyedValueLookup.alignedDatum
      directSourceFinalOccurrenceCandidateIndices
      UnaryFieldRange.values
    simpa only [Function.comp_apply] using
      (List.getD_range_getD
        (directSourceFinalScaledAtomIdentityCodes decider symbols) 0
        (directSourceFinalOccurrenceCandidateKeys decider symbols).length
        ((directSourceFinalOccurrenceCandidateKeys
          decider symbols).idxOf query) queryIndexLt)
  · intro index indexMember
    rw [directSourceFinalScaledAtomIdentityCodes_length]
    exact directSourceFinalGroupedOccurrenceIndex_lt
      decider symbols index indexMember

/-- Each grouped identity base is also the base-three quotient of its aligned
current occurrence key. -/
theorem directSourceFinalGroupedScaledAtomIdentityCodes_eq_map_div
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedScaledAtomIdentityCodes decider symbols =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map
        fun key => (key / 3) * 3 := by
  rw [directSourceFinalGroupedScaledAtomIdentityCodes_eq_map_alignedDatum]
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
        (directSourceFinalAtomIdentityCodes decider symbols).length := by
    rw [← StableOccurrenceRanks.candidateKeys_length]
    exact List.idxOf_lt_length_iff.mpr queryCandidate'
  unfold UnaryKeyedValueLookup.alignedDatum
  rw [directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
  unfold directSourceFinalScaledAtomIdentityCodes
    UnaryFieldConstantScale.values
  rw [List.getD_eq_getElem _ _ (by simpa using indexLt),
    List.getElem_map]
  have valueEq := components.1
  rw [List.getD_eq_getElem _ _ indexLt] at valueEq
  rw [valueEq]

end LeanTrominoes.PeriodicCNFStripReduction

end
