/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnitRouteEndpointDisplacement

/-! # Coordinates of the first two equally directed unit steps -/

namespace LeanTrominoes.Gadget

/-- Two equal leading direction tokens determine the first two interior
points of a unit route from its starting point. -/
theorem initial_two_unit_positions
    (points : List Cell) (origin : Cell) (direction : AxisDirection)
    (head : points.head? = some origin)
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep)
    (firstDirection : (unitSubdivisionDirections points)[0]? = some direction)
    (secondDirection : (unitSubdivisionDirections points)[1]? = some direction) :
    points.getD 1 (0, 0) = Cell.add origin direction.step ∧
      points.getD 2 (0, 0) = Cell.add origin (Cell.scale 2 direction.step) := by
  rw [unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps points unitSteps] at firstDirection secondDirection
  cases points with
  | nil => simp at head
  | cons first rest =>
      have firstEq : first = origin := Option.some.inj head
      subst first
      cases rest with
      | nil => simp [routeStepDirections] at firstDirection
      | cons second rest =>
          cases rest with
          | nil => simp [routeStepDirections] at secondDirection
          | cons third tail =>
              have firstStep := AxisDirection.add_between_step_eq_of_unitAxisStep
                (List.isChain_cons_cons.mp unitSteps).1
              have secondStep := AxisDirection.add_between_step_eq_of_unitAxisStep
                (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp unitSteps).2).1
              have firstEq : AxisDirection.between origin second = direction := by
                simpa only [routeStepDirections, List.getElem?_cons_zero, Option.some.injEq] using firstDirection
              have secondEq : AxisDirection.between second third = direction := by
                simpa only [routeStepDirections, List.getElem?_cons_succ, List.getElem?_cons_zero,
                  Option.some.injEq] using secondDirection
              rw [firstEq] at firstStep
              rw [secondEq] at secondStep
              constructor
              · simpa only [List.getD_cons_succ, List.getD_cons_zero] using firstStep
              · simp only [List.getD_cons_succ, List.getD_cons_zero]
                rw [secondStep, firstStep]
                apply Prod.ext <;> simp [Cell.add, Cell.scale] <;> ring

end LeanTrominoes.Gadget
