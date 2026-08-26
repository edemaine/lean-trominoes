/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Dedup

/-! # Deduplication of repeated and pairwise-disjoint blocks -/

namespace LeanTrominoes

/-- Last-occurrence deduplication distributes over a list of blocks that are
pairwise disjoint in their presentation order. -/
theorem List.dedup_flatMap_pairwise_disjoint
    {Key Value : Type*} [DecidableEq Value]
    (keys : List Key) (block : Key → List Value)
    (blocksDisjoint : keys.Pairwise fun first second =>
      List.Disjoint (block first) (block second)) :
    (keys.flatMap block).dedup =
      keys.flatMap fun key => (block key).dedup := by
  induction keys with
  | nil => rfl
  | cons key rest induction =>
      rw [List.pairwise_cons] at blocksDisjoint
      have headDisjoint :
          List.Disjoint (block key) (rest.flatMap block) := by
        rw [List.disjoint_left]
        intro value valueHead valueRest
        rcases List.mem_flatMap.mp valueRest with
          ⟨other, otherMember, valueOther⟩
        exact (blocksDisjoint.1 other otherMember)
          valueHead valueOther
      rw [List.flatMap_cons, headDisjoint.dedup_append,
        induction blocksDisjoint.2, List.flatMap_cons]

/-- A nonempty list of identical blocks has the same last-occurrence
deduplication as one copy of the block. -/
theorem List.dedup_flatMap_const_of_nonempty
    {Index Value : Type*} [DecidableEq Value]
    (indices : List Index) (values : List Value)
    (indicesNonempty : indices ≠ []) :
    (indices.flatMap fun _ => values).dedup = values.dedup := by
  induction indices with
  | nil => exact (indicesNonempty rfl).elim
  | cons index rest induction =>
      cases rest with
      | nil => simp
      | cons next tail =>
          have valuesSubset :
              values ⊆
                ((next :: tail).flatMap fun _ => values) := by
            intro value valueMember
            exact List.mem_flatMap.mpr
              ⟨next, by simp, valueMember⟩
          rw [List.flatMap_cons,
            valuesSubset.dedup_append_right]
          exact induction (by simp)

end LeanTrominoes
