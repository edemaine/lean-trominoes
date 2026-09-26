/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingPointBounds
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionContacts
import LeanTrominoes.PeriodicGridDrawingUnitSubdivision

/-! # Open halo bounds survive ordered unit subdivision -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem routePointsInExpandedSquare_unitSubdivide (drawing : PeriodicGridDrawing)
    (orthogonal : drawing.IsOrthogonal) (bounds : drawing.RoutePointsInExpandedSquare) :
    drawing.unitSubdivide.RoutePointsInExpandedSquare := by
  intro route member point pointMember
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  have routeOrthogonal := (isOrthogonal_iff_routes drawing).mp orthogonal original originalMember
  have target : drawing.PositionInExpandedSquare point := by
    rcases AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior routeOrthogonal pointMember with
      old | ⟨segment,segmentMember,interior⟩
    · exact bounds original originalMember point old
    · have ends := gridPolylineSegments_endpoints_mem segmentMember
      exact expanded_of_contains (bounds original originalMember _ ends.1)
        (bounds original originalMember _ ends.2) (GridSegment.contains_of_interiorContains interior)
  exact target

end LeanTrominoes.PeriodicGridDrawing
