/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMFiniteDrawingCertificate

/-! # Equivalent global-planarity form of the finite drawing verifier -/
namespace LeanTrominoes.PeriodicThreeDM.FiniteDrawingCertificate
open PeriodicGridDrawing

theorem verifies_iff_finiteContacts (p : PeriodicThreeDM) (d : PeriodicGridDrawing) (wf : p.IsWellFormed) :
    verifies p d = true ↔ compatibleCheck p d=true ∧ d.IsOrthogonal ∧
      d.SegmentEndpointsInExpandedSquare ∧ d.IsContinuouslyPlanar ∧
      d.expandedFiniteRoutePointsMeetOnlyAtEndpoints=true := by
  constructor
  · intro checked
    have raw := checked
    simp only [verifies,Bool.and_eq_true] at raw
    have compatible := compatibleCheck_spec wf raw.1
    have bounds := endpointBoundsCheck_spec raw.2.2.1
    exact ⟨raw.1,orthogonalCheck_spec raw.2.1,bounds,
      isContinuouslyPlanar_of_expandedFinite bounds compatible.2.2.2.2.1
        raw.2.2.2.1 raw.2.2.2.2.1 raw.2.2.2.2.2.1,raw.2.2.2.2.2.2⟩
  · rintro ⟨checked,orthogonal,bounds,planar,contacts⟩
    have compatible := compatibleCheck_spec wf checked
    have lengths : ∀ route ∈ d.edgeRoutes, 2≤route.length := by
      intro route member
      exact route_length_ge_two_of_compatible_of_loopless p.incidenceGraph d compatible
        p.incidenceGraph_edgesAreLoopless member
    exact verifies_complete compatible orthogonal bounds planar
      (routePointsMeetOnlyAtEndpoints_of_expandedFinite
        (routePointsInExpandedSquare_of_segmentEndpoints bounds lengths) contacts)

end LeanTrominoes.PeriodicThreeDM.FiniteDrawingCertificate
