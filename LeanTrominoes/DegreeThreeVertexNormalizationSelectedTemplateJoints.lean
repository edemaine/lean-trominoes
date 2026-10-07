/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DegreeThreeVertexNormalizationSelectedTemplateGeometry
import LeanTrominoes.GridPolylineScaledEndpointTrimNeighborhood

/-! # Selected templates meet trimmed routes only at their assigned joints -/
namespace LeanTrominoes.DegreeThreeVertexNormalization
open PeriodicOrthocrossing

theorem squareBoundaryRoute_contains_midpoint (side : VertexSide) :
    GridPolyline.RealContains (squareBoundaryRoute side) (realCell (Cell.scale 8 side.direction.step)) := by
  let segment : GridSegment := ⟨(squareBoundaryRoute side).head?.getD (0,0),
    (squareBoundaryRoute side).getLast?.getD (0,0)⟩
  have member : segment ∈ gridPolylineSegments (squareBoundaryRoute side) := by
    cases side <;> simp [segment,squareBoundaryRoute,gridPolylineSegments]
  refine ⟨segment,member,?_⟩
  apply GridSegment.realContains_of_contains
  cases side <;> simp [segment,squareBoundaryRoute,Cell.scale,VertexSide.direction,AxisDirection.step,
    GridSegment.Contains,GridSegment.IsHorizontal,GridSegment.IsVertical,GridSegment.Between]

theorem selectedTemplateAt_midpoint_contact (position : Cell) (omitted selected : VertexSide)
    (port : CanonicalVertexPort) (side : VertexSide) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (selectedTemplateAt position omitted selected port) point)
    (midpoint : point = realCell (Cell.add (Cell.scale 32 position) (Cell.scale 8 side.direction.step))) :
    point = realCell (Cell.add (Cell.scale 32 position) (selectedBoundaryPoint omitted selected port)) := by
  have original := (GridPolyline.realContains_translate_inverse _ _ _).mp contains
  have localPoint : (point.1-(Cell.scale 32 position).1,point.2-(Cell.scale 32 position).2) =
      realCell (Cell.scale 8 side.direction.step) := by
    rw [midpoint]
    simp [realCell,Cell.add]
  rw [localPoint] at original
  have contact := selectedTemplate_real_boundary_contact omitted selected port side original
    (squareBoundaryRoute_contains_midpoint side)
  have boundaryEq : Cell.scale 8 side.direction.step = selectedBoundaryPoint omitted selected port :=
    realCell_injective contact
  simpa only [boundaryEq] using midpoint

theorem selectedTemplateAt_trimmedRoute_contact {route : List Cell} (simple : GridPolyline.IsRealSimple route)
    (orthogonal : OrthogonalPolyline route) (position : Cell)
    (vertexAvoidance : GridPolyline.RealContains route (realCell position) → GridPolyline.RealIsEndpoint route (realCell position))
    (omitted selected : VertexSide) (port : CanonicalVertexPort) {point : ℝ × ℝ}
    (fanContains : GridPolyline.RealContains (selectedTemplateAt position omitted selected port) point)
    (middleContains : GridPolyline.RealContains (GridPolyline.clippedScaledRoute route) point) :
    point = realCell (Cell.add (Cell.scale 32 position) (selectedBoundaryPoint omitted selected port)) ∧
      GridPolyline.RealIsEndpoint (GridPolyline.clippedScaledRoute route) point := by
  have bounds := selectedTemplateAt_real_bounds position omitted selected port fanContains
  have contact := GridPolyline.clippedScaledRoute_neighborhood_contact simple orthogonal vertexAvoidance
    (by refine ⟨?_,?_,?_,?_⟩ <;> linarith [bounds.1,bounds.2.1,bounds.2.2.1,bounds.2.2.2]) middleContains
  obtain ⟨side,midpoint⟩ := contact.2
  exact ⟨selectedTemplateAt_midpoint_contact position omitted selected port side fanContains midpoint,contact.1⟩

end LeanTrominoes.DegreeThreeVertexNormalization
