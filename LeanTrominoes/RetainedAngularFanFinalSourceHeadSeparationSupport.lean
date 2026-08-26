/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalOuterSpokeSeparation
import LeanTrominoes.RetainedTerminalCheckpointRasterization

/-! # Support for final source-head separation -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

private theorem finalGridSegment_cons_eq
    (first : Cell)
    (rest : List Cell)
    (restLength : 2 ≤ rest.length) :
    GridSegment.mk
        (polylineLastEntrance (first :: rest))
        ((first :: rest).getLastD (0, 0)) =
      GridSegment.mk
        (polylineLastEntrance rest)
        (rest.getLastD (0, 0)) := by
  generalize reversedEq : rest.reverse = reversed
  have restEq : rest = reversed.reverse := by
    simpa using congrArg List.reverse reversedEq
  subst rest
  cases reversed with
  | nil => simp at restLength
  | cons last tail =>
      cases tail with
      | nil => simp at restLength
      | cons entrance remaining =>
          simp [polylineLastEntrance, polylineFirstExit]
          change
            (((first :: remaining.reverse) ++
                [entrance, last]).getLast?).getD (0, 0) = last
          rw [List.getLast?_append_of_ne_nil
            (first :: remaining.reverse) (by simp)]
          simp

/-- A route with at least three vertices contains its final segment after
discarding its source vertex. -/
theorem finalGridSegment_mem_tail_of_length_ge_three
    (route : List Cell)
    (lengthLarge : 3 ≤ route.length) :
    GridSegment.mk
        (polylineLastEntrance route)
        (route.getLastD (0, 0)) ∈
      gridPolylineSegments route.tail := by
  cases route with
  | nil => simp at lengthLarge
  | cons first rest =>
      have restLength : 2 ≤ rest.length := by
        simpa using lengthLarge
      rw [finalGridSegment_cons_eq first rest restLength]
      exact finalGridSegment_mem rest restLength

/-- A closed coordinate rectangle containing every vertex of an orthogonal
polyline also contains every point of its unit subdivision. -/
theorem unitSubdividePolyline_points_in_rectangle
    {route : List Cell}
    (orthogonal : OrthogonalPolyline route)
    {lower upper point : Cell}
    (bounded :
      ∀ vertex ∈ route,
        InClosedGridRectangle lower upper vertex)
    (pointMember :
      point ∈ AxisDirection.unitSubdividePolyline route) :
    InClosedGridRectangle lower upper point := by
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        orthogonal pointMember with
    originalMember | ⟨segment, segmentMember, interior⟩
  · exact bounded point originalMember
  · have endpoints := gridPolylineSegments_endpoints_mem segmentMember
    exact inClosedGridRectangle_of_segment_contains
      (bounded segment.start endpoints.1)
      (bounded segment.finish endpoints.2)
      (GridSegment.contains_of_interiorContains interior)

/-- Every point of a positioned refined Figure 7 spoke is within coordinate
radius `96` of its center. -/
theorem retainedTerminalFanFigure7SpokeRouteAt_point_within
    (center : Cell)
    (slot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanFigure7SpokeRouteAt center slot) :
    WithinCoordinateRadius 96 center point := by
  rw [← retainedTerminalFanCenteredFigure7Spoke_map_add]
    at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨offset, offsetMember, rfl⟩
  have translated :=
    (retainedTerminalFanCenteredFigure7Spoke_points_within
      slot offset offsetMember).translate center
  simpa [Cell.add] using translated

end PeriodicOrthocrossing
end LeanTrominoes
