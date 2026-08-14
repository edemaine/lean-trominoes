/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingVerticalBand
import LeanTrominoes.PeriodicThreeDMNormalizationStripRasterization

/-!
# Vertical bounds for strip-raster assignments
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- The strip raster sends every open-halo point strictly between rows `0`
and `3P`. -/
theorem stripRasterLocation_vertical_interior
    {drawing : PeriodicGridDrawing} {point : Cell}
    (inside : drawing.PositionInExpandedVerticalBand point) :
    0 < (stripRasterLocation drawing.gridSize point).2 ∧
      (stripRasterLocation drawing.gridSize point).2 <
        3 * drawing.gridSize := by
  simpa [stripRasterLocation] using
    PeriodicGridDrawing.shiftedReflectedVertical_in_threePeriods inside

/-- Membership in the recursive strip route compiler exposes the consecutive
three-point window that emitted the assignment. -/
theorem exists_route_triple_of_mem_stripRouteInteriorAssignments
    (period : Nat) (color : WireColor) :
    ∀ {route : List Cell} {assignment : NormalizedCellAssignment},
      assignment ∈ stripRouteInteriorAssignments period color route →
        ∃ leading before current after rest,
          route = leading ++ before :: current :: after :: rest ∧
            assignment =
              (stripRasterLocation period current,
                routingCellTypeAt before current after color)
  | [], _, member => by simp [stripRouteInteriorAssignments] at member
  | [_], _, member => by simp [stripRouteInteriorAssignments] at member
  | [_, _], _, member => by simp [stripRouteInteriorAssignments] at member
  | before :: current :: after :: rest, assignment, member => by
      simp only [stripRouteInteriorAssignments, List.mem_cons] at member
      rcases member with equal | tailMember
      · exact ⟨[], before, current, after, rest, by simp, equal⟩
      · rcases exists_route_triple_of_mem_stripRouteInteriorAssignments
          period color tailMember with
        ⟨leading, previous, middle, next, trailing,
          routeEquation, assignmentEquation⟩
        exact ⟨before :: leading, previous, middle, next, trailing,
          by simp [routeEquation], assignmentEquation⟩

/-- Every assignment emitted from a band-contained route occupies a strict
interior strip row. -/
theorem stripRouteInteriorAssignment_vertical_interior
    {drawing : PeriodicGridDrawing} {color : WireColor}
    {route : List Cell} {assignment : NormalizedCellAssignment}
    (routeInside : drawing.PolylineInExpandedVerticalBand route)
    (member : assignment ∈
      stripRouteInteriorAssignments drawing.gridSize color route) :
    0 < assignment.1.2 ∧ assignment.1.2 < 3 * drawing.gridSize := by
  rcases exists_route_triple_of_mem_stripRouteInteriorAssignments
      drawing.gridSize color member with
    ⟨leading, before, current, after, rest,
      routeEquation, rfl⟩
  have currentMember : current ∈ route := by
    rw [routeEquation]
    simp
  exact stripRasterLocation_vertical_interior
    (routeInside current currentMember)

end PeriodicThreeDM
end LeanTrominoes
