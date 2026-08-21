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

end List
end LeanTrominoes
