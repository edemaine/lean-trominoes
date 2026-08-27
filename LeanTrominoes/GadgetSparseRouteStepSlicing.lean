/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteStepData

/-! # Slicing exact route-step streams -/

namespace LeanTrominoes
namespace Gadget

@[simp]
theorem routeStepOffsets_length_general (points : List Cell) :
    (routeStepOffsets points).length = points.length - 1 := by
  cases points with
  | nil => simp [routeStepOffsets]
  | cons first rest =>
      rw [routeStepOffsets_length]
      simp

/-- Dropping route cells drops the same number of initial offsets. -/
@[simp]
theorem routeStepOffsets_drop (count : Nat) (points : List Cell) :
    routeStepOffsets (points.drop count) =
      (routeStepOffsets points).drop count := by
  induction count generalizing points with
  | zero => simp
  | succ count induction =>
      cases points with
      | nil => simp [routeStepOffsets]
      | cons first rest =>
          cases rest with
          | nil => simp [routeStepOffsets]
          | cons second rest =>
              simp only [List.drop_succ_cons, routeStepOffsets]
              exact induction (second :: rest)

/-- Taking one more cell than a requested offset count takes exactly that
many initial offsets. -/
theorem routeStepOffsets_take_succ
    (count : Nat) (points : List Cell) :
    routeStepOffsets (points.take (count + 1)) =
      (routeStepOffsets points).take count := by
  induction count generalizing points with
  | zero =>
      cases points <;> simp [routeStepOffsets]
  | succ count induction =>
      cases points with
      | nil => simp [routeStepOffsets]
      | cons first rest =>
          cases rest with
          | nil => simp [routeStepOffsets]
          | cons second rest =>
              simp only [Nat.add_assoc,
                List.take_succ_cons, routeStepOffsets]
              congr 1
              simpa only [List.take_succ_cons] using
                induction (second :: rest)

/-- Taking route cells takes one fewer offsets. -/
@[simp]
theorem routeStepOffsets_take (count : Nat) (points : List Cell) :
    routeStepOffsets (points.take count) =
      (routeStepOffsets points).take (count - 1) := by
  cases count with
  | zero => simp [routeStepOffsets]
  | succ count =>
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
        routeStepOffsets_take_succ count points

/-- Offset-level form of removing three cells from both ends. -/
def trimThreeOffsets (offsets : List Cell) : List Cell :=
  (offsets.drop 3).take (offsets.length - 6)

/-- The route normalizer's cell-level endpoint trimming is exactly
`trimThreeOffsets` on the corresponding offset word. -/
theorem routeStepOffsets_trim_three (points : List Cell) :
    routeStepOffsets
        ((points.drop 3).take (points.length - 6)) =
      trimThreeOffsets (routeStepOffsets points) := by
  rw [routeStepOffsets_take, routeStepOffsets_drop]
  unfold trimThreeOffsets
  rw [routeStepOffsets_length_general]
  have counts :
      points.length - 6 - 1 = points.length - 1 - 6 := by
    rw [Nat.sub_sub, Nat.sub_sub]
  rw [counts]

end Gadget
end LeanTrominoes
