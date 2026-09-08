/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedDirectionDisplacementCompiler
import LeanTrominoes.GadgetSparseRouteDirectionNormalization

/-! # Recovering unit-route starts from endpoints and compiled displacement -/

namespace LeanTrominoes.DelimitedDirectionDisplacement
open Gadget

@[simp] theorem component_add (horizontal : Bool) (first second : Cell) :
    component horizontal (Cell.add first second) = component horizontal first + component horizontal second := by
  cases horizontal <;> rfl

@[simp] theorem component_sub (horizontal : Bool) (first second : Cell) :
    component horizontal (Cell.sub first second) = component horizontal first - component horizontal second := by
  cases horizontal <;> rfl

theorem displacement_routeStepDirections (horizontal : Bool) (first : Cell) (rest : List Cell)
    (unitSteps : (first :: rest).IsChain AxisDirection.IsUnitAxisStep) :
    displacement horizontal (routeStepDirections (first :: rest)) =
      component horizontal ((first :: rest).getLastD first) - component horizontal first := by
  induction rest generalizing first with
  | nil => simp [displacement, routeStepDirections]
  | cons second rest induction =>
    have parts := List.isChain_cons_cons.mp unitSteps
    have stepEq := congrArg (component horizontal)
      (AxisDirection.add_between_step_eq_of_unitAxisStep parts.1)
    rw [component_add] at stepEq
    have remaining := induction second parts.2
    simp only [routeStepDirections, displacement, List.map_cons, List.sum_cons]
    change component horizontal (AxisDirection.between first second).step +
      displacement horizontal (routeStepDirections (second :: rest)) = _
    rw [remaining]
    simp only [List.getLastD_cons]
    omega

/-- Signed direction counts telescope to the exact endpoint difference. -/
theorem displacement_unitSubdivisionDirections (horizontal : Bool) (points : List Cell)
    (first last : Cell) (head : points.head? = some first) (endPoint : points.getLast? = some last)
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    displacement horizontal (unitSubdivisionDirections points) =
      component horizontal last - component horizontal first := by
  cases points with
  | nil => simp at head
  | cons actualFirst rest =>
    have firstEq : actualFirst = first := Option.some.inj head
    subst actualFirst
    rw [unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps _ unitSteps,
      displacement_routeStepDirections horizontal first rest unitSteps,
      List.getLastD_eq_getLast?, endPoint, Option.getD_some]

/-- The route's start is determined by its endpoint and signed direction counts. -/
theorem start_component_eq_end_sub_displacement (horizontal : Bool) (points : List Cell)
    (first last : Cell) (head : points.head? = some first) (endPoint : points.getLast? = some last)
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    component horizontal first = component horizontal last -
      displacement horizontal (unitSubdivisionDirections points) := by
  rw [displacement_unitSubdivisionDirections horizontal points first last head endPoint unitSteps]
  omega

/-- For a route with an edge, a finite first-direction header and the stored
point-deleted tail recover the complete direction word. -/
theorem firstDirection_cons_tail (first second : Cell) (rest : List Cell)
    (unitSteps : (first :: second :: rest).IsChain AxisDirection.IsUnitAxisStep) :
    AxisDirection.polylineFirstDirection (first :: second :: rest) ::
        unitSubdivisionDirections (second :: rest) =
      unitSubdivisionDirections (first :: second :: rest) := by
  have parts := List.isChain_cons_cons.mp unitSteps
  rw [unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps _ unitSteps,
    unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps _ parts.2]
  simp only [AxisDirection.polylineFirstDirection, routeStepDirections]

/-- The same displacement identity also covers empty and singleton routes;
the invalid first-direction fallback contributes zero. -/
theorem displacement_eq_first_add_tail (horizontal : Bool) (points : List Cell)
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    displacement horizontal (unitSubdivisionDirections points) =
      component horizontal (AxisDirection.polylineFirstDirection points).step +
        displacement horizontal (unitSubdivisionDirections points.tail) := by
  cases points with
  | nil => cases horizontal <;> simp [displacement, component, unitSubdivisionDirections,
      AxisDirection.polylineFirstDirection, AxisDirection.step]
  | cons first rest =>
    cases rest with
    | nil => cases horizontal <;> simp [displacement, component, unitSubdivisionDirections,
        AxisDirection.polylineFirstDirection, AxisDirection.step]
    | cons second rest =>
      rw [← firstDirection_cons_tail first second rest unitSteps]
      rfl

end LeanTrominoes.DelimitedDirectionDisplacement
