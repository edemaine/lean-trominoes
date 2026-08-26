/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupRepeatedDisjointBlocks

/-! # Stable deduplication after repeating mapped values -/

namespace LeanTrominoes

/-- Replacing each mapped value by one nonempty run of identical copies does
not change last-occurrence-preserving deduplication. -/
theorem List.dedup_flatMap_repeated_map
    {Source Index Target : Type*} [DecidableEq Target]
    (source : List Source) (indices : List Index)
    (mapping : Source → Target) (indicesNonempty : indices ≠ []) :
    (source.flatMap fun value =>
      indices.map fun _ => mapping value).dedup =
        (source.map mapping).dedup := by
  cases indices with
  | nil => exact (indicesNonempty rfl).elim
  | cons firstIndex indices =>
    induction source with
    | nil => rfl
    | cons value rest induction =>
      let block := (firstIndex :: indices).map fun _ => mapping value
      let tail := rest.flatMap fun item =>
        (firstIndex :: indices).map fun _ => mapping item
      by_cases later : mapping value ∈ rest.map mapping
      · have blockSubset : block ⊆ tail := by
          intro target targetMember
          have targetEq : target = mapping value := by
            rcases List.mem_map.mp targetMember with
              ⟨index, _indexMember, targetEq⟩
            exact targetEq.symm
          rcases List.mem_map.mp later with
            ⟨item, itemMember, itemEq⟩
          let index := firstIndex
          have indexMember : index ∈ firstIndex :: indices := by simp [index]
          subst target
          exact List.mem_flatMap.mpr
            ⟨item, itemMember,
              List.mem_map.mpr ⟨index, indexMember, itemEq⟩⟩
        change (block ++ tail).dedup = _
        rw [blockSubset.dedup_append_right]
        rw [induction, List.map_cons,
          List.dedup_cons_of_mem later]
      · have blockDisjoint : List.Disjoint block tail := by
          rw [List.disjoint_left]
          intro target targetMember targetTailMember
          rcases List.mem_map.mp targetMember with
            ⟨index, _indexMember, targetEq⟩
          rcases List.mem_flatMap.mp targetTailMember with
            ⟨item, itemMember, targetItemMember⟩
          rcases List.mem_map.mp targetItemMember with
            ⟨itemIndex, _itemIndexMember, itemEq⟩
          apply later
          exact List.mem_map.mpr
            ⟨item, itemMember, itemEq.trans targetEq.symm⟩
        have blockDedup : block.dedup = [mapping value] := by
          unfold block
          rw [List.map_const']
          exact List.replicate_dedup (by simp)
        change (block ++ tail).dedup = _
        rw [blockDisjoint.dedup_append, blockDedup, induction,
          List.map_cons, List.dedup_cons_of_notMem later]
        rfl

end LeanTrominoes
