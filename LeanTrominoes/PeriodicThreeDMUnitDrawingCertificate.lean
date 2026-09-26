/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMFiniteDrawingCertificate
import LeanTrominoes.PeriodicGridDrawingUnitSubdivisionBounds
import LeanTrominoes.PeriodicGridDrawingUnitSubdivisionContinuousPlanarity
import LeanTrominoes.PeriodicGridDrawingUnitSubdivisionRibbon

/-! # Finite certificates for unit-subdivided 3DM drawings -/
namespace LeanTrominoes.PeriodicThreeDM.FiniteDrawingCertificate

theorem verifies_unitSubdivide (problem : PeriodicThreeDM) (drawing : PeriodicGridDrawing)
    (compatible : drawing.IsCompatible problem.incidenceGraph)
    (orthogonal : drawing.IsOrthogonal)
    (bounds : drawing.RoutePointsInExpandedSquare)
    (continuous : drawing.IsContinuouslyPlanar)
    (separated : drawing.LiftedRoutesAvoidEachOther)
    (simple : ∀ route ∈ drawing.edgeRoutes, LocalIncidenceDrawing.RouteIsSimple route) :
    verifies problem drawing.unitSubdivide = true := by
  have nonempty : ∀ route ∈ drawing.edgeRoutes, route ≠ [] := by
    intro route member empty
    have length := PeriodicGridDrawing.route_length_ge_two_of_compatible_of_loopless
      problem.incidenceGraph drawing compatible problem.incidenceGraph_edgesAreLoopless member
    simp [empty] at length
  exact verifies_complete
    (PeriodicGridDrawing.isCompatible_unitSubdivide problem.incidenceGraph drawing compatible orthogonal)
    (PeriodicGridDrawing.isOrthogonal_unitSubdivide drawing orthogonal)
    (PeriodicGridDrawing.segmentEndpointsInExpandedSquare_of_routePoints
      (PeriodicGridDrawing.routePointsInExpandedSquare_unitSubdivide drawing orthogonal bounds))
    (PeriodicGridDrawing.isContinuouslyPlanar_unitSubdivide drawing continuous orthogonal)
    (PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_unitSubdivide drawing separated orthogonal nonempty simple)

end LeanTrominoes.PeriodicThreeDM.FiniteDrawingCertificate
