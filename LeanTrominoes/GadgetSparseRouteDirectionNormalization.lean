/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitOffsets
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionJoin
import LeanTrominoes.OrthogonalPolylineLoopErasure

/-! # Direction words through orthogonal route normalization -/

namespace LeanTrominoes
namespace Gadget

open PeriodicOrthocrossing

/-- On an already unit-step route, segment-major subdivision directions are
its ordinary consecutive-edge directions. -/
theorem unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
    (points : List Cell)
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    unitSubdivisionDirections points = routeStepDirections points := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [unitSubdivisionDirections, routeStepDirections]
  | cons_cons first second rest _ induction =>
      have firstUnit : AxisDirection.IsUnitAxisStep first second :=
        (List.isChain_cons_cons.mp unitSteps).1
      have remainingUnitSteps :
          (second :: rest).IsChain AxisDirection.IsUnitAxisStep :=
        (List.isChain_cons_cons.mp unitSteps).2
      simp only [unitSubdivisionDirections, routeStepDirections,
        segmentLength_eq_one_of_unitAxisStep firstUnit,
        List.replicate_one, List.singleton_append, List.cons.injEq]
      exact ⟨True.intro, induction second remainingUnitSteps⟩

/-- Ordered unit subdivision changes the point representation of an
orthogonal polyline but not its complete direction word. -/
theorem unitSubdivisionDirections_unitSubdividePolyline
    (points : List Cell)
    (orthogonal : OrthogonalPolyline points) :
    unitSubdivisionDirections
        (AxisDirection.unitSubdividePolyline points) =
      unitSubdivisionDirections points := by
  induction points using List.twoStepInduction with
  | nil =>
      simp [unitSubdivisionDirections]
  | singleton point =>
      simp [unitSubdivisionDirections]
  | cons_cons first second rest _ induction =>
      have parts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            OrthogonalPolyline (second :: rest))
      have firstLength :
          2 ≤ (AxisDirection.unitSegmentPoints first second).length := by
        rw [AxisDirection.unitSegmentPoints_length]
        have positive :=
          AxisDirection.segmentLength_positive_of_axisAligned parts.1
        omega
      have boundary :
          (AxisDirection.unitSegmentPoints first second).getLast? =
            (AxisDirection.unitSubdividePolyline
              (second :: rest)).head? := by
        rw [AxisDirection.unitSegmentPoints_getLast? parts.1]
        simpa using (AxisDirection.unitSubdividePolyline_head?
          (points := second :: rest) (by simp)).symm
      rw [AxisDirection.unitSubdividePolyline]
      change unitSubdivisionDirections
          (joinPolylines
            (AxisDirection.unitSegmentPoints first second)
            (AxisDirection.unitSubdividePolyline (second :: rest))) = _
      rw [unitSubdivisionDirections_joinPolylines firstLength boundary]
      rw [unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
        (AxisDirection.unitSegmentPoints first second)
        (AxisDirection.unitSegmentPoints_unitSteps parts.1)]
      rw [routeStepDirections_unitSegmentPoints parts.1]
      rw [induction second parts.2]
      rw [unitSubdivisionDirections]

/-- On a simple orthogonal route, loop-erasing normalization is invisible at
the direction-stream boundary. -/
theorem unitSubdivisionDirections_normalizeOrthogonalPolyline_of_simple
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal : OrthogonalPolyline points)
    (simple : LocalIncidenceDrawing.RouteIsSimple points) :
    unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline points) =
      unitSubdivisionDirections points := by
  rw [AxisDirection.normalizeOrthogonalPolyline_eq_unitSubdividePolyline_of_simple
    nonempty orthogonal simple]
  exact unitSubdivisionDirections_unitSubdividePolyline points orthogonal

end Gadget
end LeanTrominoes
