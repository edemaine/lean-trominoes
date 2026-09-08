/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.FinalFanQueryRankKeyPermutation
import LeanTrominoes.ListDedupDisjointBlocks
import LeanTrominoes.StableOccurrenceRanksGroupedIndices

/-! # Exact source-variable order of distinct final-fan query keys -/

namespace LeanTrominoes.FinalFanQueryRanks

private theorem dedup_keyBlock (value count : Nat)
    (positive : 0 < count) (countLe : count ≤ 3) :
    ((block (BoundedPositiveCountPreds.boundedPositiveCountPred count)).map
      (fun rank => value * 3 + rank.val)).dedup =
      (List.range count).map (fun rank => value * 3 + rank) := by
  interval_cases count <;>
    simp [block, selectedRank, BoundedPositiveCountPreds.boundedPositiveCountPred,
      List.range_succ]

/-- Stable distinct fan queries follow the source's last-representative
variable order and increasing active rank, with all fallback copies removed. -/
theorem dedup_keyedBlocks_eq (values : List Nat)
    (countLe : ∀ value ∈ values, values.count value ≤ 3) :
    (keyedBlocks values).dedup = values.dedup.flatMap fun value =>
      (List.range (values.count value)).map (fun rank => value * 3 + rank) := by
  unfold keyedBlocks
  rw [List.dedup_flatMap_disjoint_blocks]
  · apply List.flatMap_congr
    intro value member
    have member := List.mem_dedup.mp member
    exact dedup_keyBlock value (values.count value)
      (List.count_pos_iff.mpr member) (countLe value member)
  · intro first second different
    rw [List.disjoint_left]
    intro key firstMember secondMember
    obtain ⟨firstRank, _, firstEq⟩ := List.mem_map.mp firstMember
    obtain ⟨secondRank, _, secondEq⟩ := List.mem_map.mp secondMember
    have := firstRank.isLt
    have := secondRank.isLt
    omega

/-- Looking up the distinct fan keys in the stable candidate column yields
exactly the source-variable-major list of presentation indices. -/
theorem dedup_keyedBlocks_map_idxOf (values : List Nat)
    (countLe : ∀ value ∈ values, values.count value ≤ 3) :
    ((keyedBlocks values).dedup.map
      (fun key => (StableOccurrenceRanks.candidateKeys values).idxOf key)) =
      StableOccurrenceRanks.groupedIndices values := by
  rw [dedup_keyedBlocks_eq values countLe, List.map_flatMap]
  unfold StableOccurrenceRanks.groupedIndices
  apply List.flatMap_congr
  intro value _member
  rw [List.map_map]
  apply List.ext_getElem
  · simp
  · intro index firstLt secondLt
    have rankLt : index < values.count value := by simpa using firstLt
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
    rw [StableOccurrenceRanks.candidateKeys_idxOf_rank values countLe value index rankLt]
    exact List.getD_eq_getElem _ _ secondLt

end LeanTrominoes.FinalFanQueryRanks
