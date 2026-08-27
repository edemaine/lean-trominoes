/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionNormalization

/-! # Prefixes and suffixes of unit-route direction words -/

namespace LeanTrominoes
namespace Gadget

/-- Dropping `count` route points drops the same number of consecutive-edge
directions. -/
@[simp] theorem routeStepDirections_drop
    (count : Nat) (points : List Cell) :
    routeStepDirections (points.drop count) =
      (routeStepDirections points).drop count := by
  induction count generalizing points with
  | zero => simp
  | succ count induction =>
      cases points with
      | nil => simp [routeStepDirections]
      | cons first rest =>
          cases rest with
          | nil => simp [routeStepDirections]
          | cons second tail =>
              simp [routeStepDirections, induction]

/-- Keeping `count + 1` route points keeps the first `count`
consecutive-edge directions. -/
@[simp] theorem routeStepDirections_take_succ
    (count : Nat) (points : List Cell) :
    routeStepDirections (points.take (count + 1)) =
      (routeStepDirections points).take count := by
  induction count generalizing points with
  | zero =>
      cases points <;> simp [routeStepDirections]
  | succ count induction =>
      cases points with
      | nil => simp [routeStepDirections]
      | cons first rest =>
          cases rest with
          | nil => simp [routeStepDirections]
          | cons second tail =>
              simp only [List.take_succ_cons, routeStepDirections,
                List.cons.injEq, true_and]
              simpa only [List.take_succ_cons] using
                induction (second :: tail)

/-- On a unit route, a point suffix exposes the corresponding direction-word
suffix. -/
theorem unitSubdivisionDirections_drop_of_unitSteps
    (count : Nat) (points : List Cell)
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    unitSubdivisionDirections (points.drop count) =
      (unitSubdivisionDirections points).drop count := by
  rw [unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
    (points.drop count) (unitSteps.drop count)]
  rw [routeStepDirections_drop]
  rw [unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
    points unitSteps]

/-- On a unit route, a point prefix of length `count + 1` exposes the first
`count` directions. -/
theorem unitSubdivisionDirections_take_succ_of_unitSteps
    (count : Nat) (points : List Cell)
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    unitSubdivisionDirections (points.take (count + 1)) =
      (unitSubdivisionDirections points).take count := by
  rw [unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
    (points.take (count + 1)) (unitSteps.take (count + 1))]
  rw [routeStepDirections_take_succ]
  rw [unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
    points unitSteps]

/-- The two-point prefix used by polarity subdivision contains precisely the
first incoming direction. -/
theorem unitSubdivisionDirections_take_two_of_unitSteps
    (points : List Cell)
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    unitSubdivisionDirections (points.take 2) =
      (unitSubdivisionDirections points).take 1 := by
  simpa using
    unitSubdivisionDirections_take_succ_of_unitSteps 1 points unitSteps

end Gadget
end LeanTrominoes
