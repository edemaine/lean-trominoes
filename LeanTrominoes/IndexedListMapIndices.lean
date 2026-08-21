/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Batteries.Data.List.Lemmas

/-! # Index preservation for list maps and prefixes -/

namespace LeanTrominoes
namespace List

universe u v

/-- Mapping a value together with its stable index and then re-indexing
preserves that same index. -/
theorem indexedMap_zipIdx
    {α : Type u} {β : Type v} (values : List α)
    (mapAt : α → Nat → β) (start : Nat) :
    (((values.zipIdx start).map fun tagged =>
        mapAt tagged.1 tagged.2).zipIdx start) =
      (values.zipIdx start).map fun tagged =>
        (mapAt tagged.1 tagged.2, tagged.2) := by
  induction values generalizing start with
  | nil => rfl
  | cons value values induction =>
      simp only [List.zipIdx_cons, List.map_cons]
      rw [induction (start + 1)]

/-- Taking a prefix commutes exactly with stable list indexing. -/
theorem take_zipIdx
    {α : Type u} (values : List α) (count start : Nat) :
    (values.zipIdx start).take count =
      (values.take count).zipIdx start := by
  induction values generalizing count start with
  | nil => simp
  | cons value values induction =>
      cases count with
      | zero => rfl
      | succ count =>
          simp only [List.zipIdx_cons, List.take_succ_cons]
          rw [induction count (start + 1)]

/-- General-start form of affine indexing for fixed-width flat-map blocks. -/
theorem flatMap_zipIdx_fixed_from
    {α : Type u} {β : Type v}
    (values : List α) (block : α → List β)
    (width start outerStart : Nat)
    (blockLength : ∀ value, (block value).length = width) :
    (values.flatMap block).zipIdx (start + width * outerStart) =
      (values.zipIdx outerStart).flatMap fun tagged =>
        (block tagged.1).zipIdx (start + width * tagged.2) := by
  induction values generalizing outerStart with
  | nil => simp
  | cons value values induction =>
      rw [List.flatMap_cons, List.zipIdx_append,
        List.zipIdx_cons, List.flatMap_cons]
      rw [blockLength value]
      have tail := induction (outerStart := outerStart + 1)
      rw [show start + width * outerStart + width =
          start + width * (outerStart + 1) by
        rw [Nat.mul_add, Nat.mul_one]
        omega,
        tail]

/-- Indexing a flat map of fixed-width blocks assigns affine indices to each
block, universe-polymorphically. -/
theorem flatMap_zipIdx_fixed
    {α : Type u} {β : Type v}
    (values : List α) (block : α → List β)
    (width start : Nat)
    (blockLength : ∀ value, (block value).length = width) :
    (values.flatMap block).zipIdx start =
      values.zipIdx.flatMap fun tagged =>
        (block tagged.1).zipIdx (start + width * tagged.2) := by
  simpa using flatMap_zipIdx_fixed_from
    values block width start 0 blockLength

end List
end LeanTrominoes
