/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionNormalization
import LeanTrominoes.OrthogonalPolylineLoopErasureRightLocalization

/-! # Directional extensionality of orthogonal route normalization -/

namespace LeanTrominoes

namespace Gadget

/-- A unit-step route is determined by its first point and its successive
direction word. -/
theorem route_eq_of_head?_eq_of_routeStepDirections_eq_of_unitSteps
    {first second : List Cell}
    (firstUnitSteps : first.IsChain AxisDirection.IsUnitAxisStep)
    (secondUnitSteps : second.IsChain AxisDirection.IsUnitAxisStep)
    (headEq : first.head? = second.head?)
    (directionsEq :
      routeStepDirections first = routeStepDirections second) :
    first = second := by
  cases first with
  | nil =>
      cases second with
      | nil => rfl
      | cons head tail => simp at headEq
  | cons firstHead firstTail =>
      cases second with
      | nil => simp at headEq
      | cons secondHead secondTail =>
          simp only [List.head?_cons, Option.some.injEq] at headEq
          subst secondHead
          rw [← rebuildRoute_routeStepDirections
              firstHead firstTail firstUnitSteps,
            directionsEq,
            rebuildRoute_routeStepDirections
              firstHead secondTail secondUnitSteps]

end Gadget

namespace AxisDirection

open PeriodicOrthocrossing

/-- Two nonempty orthogonal polylines with the same start and complete
unit-subdivision direction word have the same ordered unit subdivision. -/
theorem unitSubdividePolyline_eq_of_head?_eq_of_directions_eq
    {first second : List Cell}
    (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ [])
    (firstOrthogonal : OrthogonalPolyline first)
    (secondOrthogonal : OrthogonalPolyline second)
    (headEq : first.head? = second.head?)
    (directionsEq :
      Gadget.unitSubdivisionDirections first =
        Gadget.unitSubdivisionDirections second) :
    unitSubdividePolyline first = unitSubdividePolyline second := by
  apply
    Gadget.route_eq_of_head?_eq_of_routeStepDirections_eq_of_unitSteps
      (unitSubdividePolyline_unitSteps firstOrthogonal)
      (unitSubdividePolyline_unitSteps secondOrthogonal)
  · rw [unitSubdividePolyline_head? firstNonempty,
      unitSubdividePolyline_head? secondNonempty]
    exact headEq
  · rw [← Gadget.unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
        (unitSubdividePolyline first)
        (unitSubdividePolyline_unitSteps firstOrthogonal),
      ← Gadget.unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
        (unitSubdividePolyline second)
        (unitSubdividePolyline_unitSteps secondOrthogonal),
      Gadget.unitSubdivisionDirections_unitSubdividePolyline
        first firstOrthogonal,
      Gadget.unitSubdivisionDirections_unitSubdividePolyline
        second secondOrthogonal]
    exact directionsEq

/-- Consequently, route normalization depends only on the initial point and
the complete unit-subdivision direction word, not on collinear subdivision
vertices in the input polyline. -/
theorem normalizeOrthogonalPolyline_eq_of_head?_eq_of_directions_eq
    {first second : List Cell}
    (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ [])
    (firstOrthogonal : OrthogonalPolyline first)
    (secondOrthogonal : OrthogonalPolyline second)
    (headEq : first.head? = second.head?)
    (directionsEq :
      Gadget.unitSubdivisionDirections first =
        Gadget.unitSubdivisionDirections second) :
    normalizeOrthogonalPolyline first =
      normalizeOrthogonalPolyline second := by
  rw [normalizeOrthogonalPolyline_eq_listLoopErase
      firstNonempty firstOrthogonal,
    normalizeOrthogonalPolyline_eq_listLoopErase
      secondNonempty secondOrthogonal,
    unitSubdividePolyline_eq_of_head?_eq_of_directions_eq
      firstNonempty secondNonempty firstOrthogonal secondOrthogonal
      headEq directionsEq]

end AxisDirection
end LeanTrominoes
