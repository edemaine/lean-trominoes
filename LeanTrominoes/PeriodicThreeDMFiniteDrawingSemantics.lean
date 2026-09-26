/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMFiniteDrawingCertificate

/-! # Exact geometric meaning of the native finite 3DM drawing verifier -/
namespace LeanTrominoes.PeriodicThreeDM.FiniteDrawingCertificate

theorem verifies_iff {problem : PeriodicThreeDM} {drawing : PeriodicGridDrawing}
    (wf : problem.IsWellFormed) : verifies problem drawing = true ↔
      drawing.IsCompatible problem.incidenceGraph ∧ drawing.IsOrthogonal ∧
      drawing.SegmentEndpointsInExpandedSquare ∧ drawing.IsContinuouslyPlanar ∧
      drawing.RoutePointsMeetOnlyAtEndpoints := by
  constructor
  · intro checked
    simp only [verifies,Bool.and_eq_true] at checked
    have compatible := compatibleCheck_spec wf checked.1
    have orthogonal := orthogonalCheck_spec checked.2.1
    have bounds := endpointBoundsCheck_spec checked.2.2.1
    have planar := PeriodicGridDrawing.isContinuouslyPlanar_of_expandedFinite
      bounds compatible.2.2.2.2.1 checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2.1
    have lengths : ∀ route ∈ drawing.edgeRoutes, 2 ≤ route.length := by
      intro route member
      exact PeriodicGridDrawing.route_length_ge_two_of_compatible_of_loopless
        problem.incidenceGraph drawing compatible problem.incidenceGraph_edgesAreLoopless member
    have points := PeriodicGridDrawing.routePointsInExpandedSquare_of_segmentEndpoints bounds lengths
    have contacts := PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_of_expandedFinite
      points checked.2.2.2.2.2.2
    exact ⟨compatible,orthogonal,bounds,planar,contacts⟩
  · rintro ⟨compatible,orthogonal,bounds,planar,contacts⟩
    exact verifies_complete compatible orthogonal bounds planar contacts

end LeanTrominoes.PeriodicThreeDM.FiniteDrawingCertificate
