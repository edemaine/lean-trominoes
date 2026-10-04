/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMIncidenceVertexCoverage
import LeanTrominoes.FiniteThreeDMGraphOffsets
import LeanTrominoes.FiniteGridDrawingPaddingPlanarity
import LeanTrominoes.PeriodicContinuousPlanarThreeDM
import LeanTrominoes.PeriodicGridDrawingPointBounds

/-! # A zero-offset planar 3DM presentation can be padded inside one square -/
namespace LeanTrominoes.PeriodicThreeDM

def ContinuousPlanarPresentation.finitePad {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation) (zero : problem.ZeroOffsets)
    (bounds : presentation.drawing.SegmentEndpointsInExpandedSquare) :
    problem.ContinuousPlanarPresentation where
  drawing := presentation.drawing.finitePad
  problemWellFormed := presentation.problemWellFormed
  compatible := PeriodicGridDrawing.finitePad_isCompatible presentation.compatible
    (incidenceGraph_zeroOffsets problem zero)
  orthogonal := PeriodicGridDrawing.finitePad_isOrthogonal presentation.orthogonal
  planar := (PeriodicGridDrawing.finitePad_isContinuouslyPlanar bounds
    presentation.compatible.2.2.2.2.1 presentation.continuouslyPlanar).1
  continuouslyPlanar := PeriodicGridDrawing.finitePad_isContinuouslyPlanar bounds
    presentation.compatible.2.2.2.2.1 presentation.continuouslyPlanar

theorem ContinuousPlanarPresentation.finitePad_routePointsInFundamentalSquare
    {problem : PeriodicThreeDM} (presentation : problem.ContinuousPlanarPresentation)
    (zero : problem.ZeroOffsets) (bounds : presentation.drawing.SegmentEndpointsInExpandedSquare) :
    (presentation.finitePad zero bounds).drawing.RoutePointsInFundamentalSquare := by
  have sourceInside : presentation.drawing.RoutePointsInExpandedSquare :=
    PeriodicGridDrawing.routePointsInExpandedSquare_of_segmentEndpoints bounds
      (fun route member => PeriodicGridDrawing.route_length_ge_two_of_compatible_of_loopless
        problem.incidenceGraph presentation.drawing presentation.compatible
        problem.incidenceGraph_edgesAreLoopless member)
  intro route routeMember point pointMember
  obtain ⟨originalRoute,originalRouteMember,rfl⟩ := List.mem_map.mp routeMember
  obtain ⟨originalPoint,originalPointMember,rfl⟩ := List.mem_map.mp pointMember
  exact PeriodicGridDrawing.finitePad_point_inFundamental
    (sourceInside _ originalRouteMember _ originalPointMember)

end LeanTrominoes.PeriodicThreeDM
