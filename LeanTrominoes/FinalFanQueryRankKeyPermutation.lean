/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FinalFanQueryRankKeyCoverage
import LeanTrominoes.StableOccurrenceRankCandidateKeyNodup

/-! # Exact coverage of finite fan rank keys -/

namespace LeanTrominoes.FinalFanQueryRanks

/-- When an identity occurs at most three times, every genuine stable rank
appears in the finite active-or-fallback fan block. -/
theorem rank_mem_block_of_lt_count_le_three
    (count rank : Nat) (rankLt : rank < count) (countLe : count <= 3) :
    ∃ selected ∈ block
        (BoundedPositiveCountPreds.boundedPositiveCountPred count),
      selected.val = rank := by
  interval_cases count <;> interval_cases rank <;>
    simp_all [BoundedPositiveCountPreds.boundedPositiveCountPred,
      block, selectedRank]

/-- Under the final-formula occurrence bound, the finite fan queries cover
all stable occurrence keys, not just a subset of them. -/
theorem candidateKeys_subset_keyedBlocks
    (values : List Nat)
    (countLe : ∀ value ∈ values, values.count value <= 3) :
    StableOccurrenceRanks.candidateKeys values ⊆ keyedBlocks values := by
  intro query queryMember
  rcases List.mem_iff_getElem.mp queryMember with
    ⟨index, indexLt, queryEq⟩
  have valueIndexLt : index < values.length := by
    simpa using indexLt
  let value := values[index]
  let rank := (StableOccurrenceRanks.ranks values)[index]'(by
    simpa using valueIndexLt)
  have rankEq : rank = (values.take index).count value := by
    have lookup := StableOccurrenceRanks.ranks_getElem? values index
    have rankIndexLt :
        index < (StableOccurrenceRanks.ranks values).length := by
      simpa using valueIndexLt
    simpa only [rank, value,
      List.getElem?_eq_getElem rankIndexLt,
      List.getElem?_eq_getElem valueIndexLt,
      Option.map_some, Option.some.injEq] using lookup
  have rankLt : rank < values.count value := by
    rw [rankEq]
    exact @List.count_getElem_take_lt_count Nat _ (by infer_instance)
      values index valueIndexLt
  have valueMember : value ∈ values := List.getElem_mem valueIndexLt
  have rankLeThree : rank < 3 :=
    lt_of_lt_of_le rankLt (countLe value valueMember)
  rcases rank_mem_block_of_lt_count_le_three
      (values.count value) rank rankLt (countLe value valueMember) with
    ⟨selected, selectedMember, selectedVal⟩
  apply List.mem_flatMap.mpr
  refine ⟨value, valueMember, ?_⟩
  apply List.mem_map.mpr
  refine ⟨selected, selectedMember, ?_⟩
  have queryAt :
      (StableOccurrenceRanks.candidateKeys values)[index]'indexLt =
        value * 3 + rank := by
    simp [StableOccurrenceRanks.candidateKeys, value, rank]
  rw [selectedVal, ← queryAt, queryEq]

/-- Stable deduplication of the three fan queries per presented occurrence
is a permutation of the canonical stable occurrence-key column. -/
theorem dedup_keyedBlocks_perm_candidateKeys
    (values : List Nat)
    (countLe : ∀ value ∈ values, values.count value <= 3) :
    (keyedBlocks values).dedup.Perm
      (StableOccurrenceRanks.candidateKeys values) := by
  apply List.perm_of_nodup_nodup_toFinset_eq
    (List.nodup_dedup _)
    (StableOccurrenceRanks.candidateKeys_nodup_of_count_le_three
      values countLe)
  apply Finset.ext
  intro query
  simp only [List.mem_toFinset, List.mem_dedup]
  constructor
  · intro member
    exact keyedBlocks_subset_candidateKeys values member
  · intro member
    exact candidateKeys_subset_keyedBlocks values countLe member

end LeanTrominoes.FinalFanQueryRanks
