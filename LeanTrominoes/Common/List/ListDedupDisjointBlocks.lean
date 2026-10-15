/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Dedup

/-! # Deduplication of repeated disjoint list blocks -/

namespace LeanTrominoes

/-- For blocks whose values identify their key, last-occurrence-preserving
deduplication acts on both the keys and the individual blocks. -/
theorem List.dedup_flatMap_disjoint_blocks
    {Key Value : Type*}
    [DecidableEq Key] [DecidableEq Value]
    (keys : List Key)
    (block : Key → List Value)
    (blockDisjoint :
      ∀ {first second}, first ≠ second →
        List.Disjoint (block first) (block second)) :
    (keys.flatMap block).dedup =
      keys.dedup.flatMap (fun key => (block key).dedup) := by
  induction keys with
  | nil =>
      rfl
  | cons key rest induction =>
      by_cases keyMember : key ∈ rest
      · have blockSubset : block key ⊆ rest.flatMap block := by
          intro value valueMember
          exact List.mem_flatMap.mpr
            ⟨key, keyMember, valueMember⟩
        rw [List.flatMap_cons,
          blockSubset.dedup_append_right,
          List.dedup_cons_of_mem keyMember,
          induction]
      · have blocksDisjoint :
            List.Disjoint (block key) (rest.flatMap block) := by
          rw [List.disjoint_left]
          intro value valueMember valueRestMember
          rcases List.mem_flatMap.mp valueRestMember with
            ⟨other, otherMember, valueOtherMember⟩
          have keyNe : key ≠ other := by
            intro equal
            subst other
            exact keyMember otherMember
          exact (blockDisjoint keyNe)
            valueMember valueOtherMember
        rw [List.flatMap_cons,
          blocksDisjoint.dedup_append,
          List.dedup_cons_of_notMem keyMember,
          List.flatMap_cons,
          induction]

/-- Duplicate-free disjoint blocks need only deduplicate their keys. -/
theorem List.dedup_flatMap_blocks
    {Key Value : Type*} [DecidableEq Key] [DecidableEq Value]
    (keys : List Key) (block : Key → List Value)
    (blockNodup : ∀ key, (block key).Nodup)
    (blockDisjoint : ∀ {first second}, first ≠ second →
      List.Disjoint (block first) (block second)) :
    (keys.flatMap block).dedup = keys.dedup.flatMap block := by
  rw [List.dedup_flatMap_disjoint_blocks keys block blockDisjoint]
  simp only [List.dedup_eq_self.mpr (blockNodup _)]

end LeanTrominoes
