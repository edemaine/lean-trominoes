/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanAnnulusRefinedRoutes
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Positioning the retained angular-fan routes

The finite router is certified once around the origin.  This file translates
that certificate to an arbitrary variable center.  Common translation
preserves exact endpoints, orthogonality, square-shell bounds, and strict
continuous separation.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Common translation preserves contact-free continuous route separation. -/
theorem RoutesStrictlyAvoidEachOther.map_add
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second)
    (offset : Cell) :
    RoutesStrictlyAvoidEachOther
      (first.map (Cell.add offset))
      (second.map (Cell.add offset)) := by
  unfold RoutesStrictlyAvoidEachOther at strict ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstSegment firstMember secondSegment secondMember meet
    rw [gridPolylineSegments_map_add] at firstMember secondMember
    rcases List.mem_map.mp firstMember with
      ⟨sourceFirst, sourceFirstMember, rfl⟩
    rcases List.mem_map.mp secondMember with
      ⟨sourceSecond, sourceSecondMember, rfl⟩
    apply strict.1 sourceFirst sourceFirstMember
      sourceSecond sourceSecondMember
    exact
      (GridSegment.interiorsMeet_translate_both_iff
        sourceFirst sourceSecond offset).mp meet
  · intro firstPoint firstMember secondSegment secondMember contains
    rcases List.mem_map.mp firstMember with
      ⟨sourcePoint, sourcePointMember, rfl⟩
    rw [gridPolylineSegments_map_add] at secondMember
    rcases List.mem_map.mp secondMember with
      ⟨sourceSegment, sourceSegmentMember, rfl⟩
    apply strict.2.1 sourcePoint sourcePointMember
      sourceSegment sourceSegmentMember
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        sourceSegment offset sourcePoint).mp
        (by simpa [Cell.add, add_comm] using contains)
  · intro secondPoint secondMember firstSegment firstMember contains
    rcases List.mem_map.mp secondMember with
      ⟨sourcePoint, sourcePointMember, rfl⟩
    rw [gridPolylineSegments_map_add] at firstMember
    rcases List.mem_map.mp firstMember with
      ⟨sourceSegment, sourceSegmentMember, rfl⟩
    apply strict.2.2.1 sourcePoint sourcePointMember
      sourceSegment sourceSegmentMember
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        sourceSegment offset sourcePoint).mp
        (by simpa [Cell.add, add_comm] using contains)
  · intro firstPoint firstMember secondPoint secondMember equal
    rcases List.mem_map.mp firstMember with
      ⟨sourceFirst, sourceFirstMember, rfl⟩
    rcases List.mem_map.mp secondMember with
      ⟨sourceSecond, sourceSecondMember, rfl⟩
    exact strict.2.2.2 sourceFirst sourceFirstMember
      sourceSecond sourceSecondMember
      (cell_add_left_injective offset equal)

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Complete refined fan route translated to an arbitrary variable center. -/
def retainedTerminalFanRefinedRouteAt
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  (retainedTerminalFanRefinedRoute direction slot).map
    (Cell.add center)

/-- A positioned route starts at its positioned refined fan-facing port. -/
@[simp]
theorem retainedTerminalFanRefinedRouteAt_head?
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanRefinedRouteAt
      center direction slot).head? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (retainedTerminalFanPortOffset
                (retainedTerminalFanPort direction slot)))) := by
  simp [retainedTerminalFanRefinedRouteAt]

/-- A positioned route ends at its positioned refined Figure 7 boundary
site. -/
@[simp]
theorem retainedTerminalFanRefinedRouteAt_getLast?
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanRefinedRouteAt
      center direction slot).getLast? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val))) := by
  simp [retainedTerminalFanRefinedRouteAt]

/-- Every positioned complete route remains orthogonal. -/
theorem retainedTerminalFanRefinedRouteAt_orthogonal
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanRefinedRouteAt
        center direction slot) := by
  exact
    OccurrenceSplitRing.PeriodicOrthocrossing.OrthogonalPolyline.map_add
      (retainedTerminalFanRefinedRoute_orthogonal
        direction slot)
      center

/-- Every listed point of a positioned route stays in the translated
radius-264 outer frame. -/
theorem retainedTerminalFanRefinedRouteAt_points_within_outer_frame
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanRefinedRouteAt
        center direction slot) :
    WithinCoordinateRadius
      (33 * retainedTerminalFanRoutingRefinement)
      center point := by
  rcases List.mem_map.mp pointMember with
    ⟨sourcePoint, sourcePointMember, rfl⟩
  have base :=
    retainedTerminalFanRefinedRoute_points_within_outer_frame
      direction slot sourcePoint sourcePointMember
  simpa using base.translate center

/-- Every listed point of a positioned complete route stays outside the
translated refined Figure 7 interior. -/
theorem retainedTerminalFanRefinedRouteAt_points_outside_fan
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanRefinedRouteAt
        center direction slot) :
    ¬ WithinCoordinateRadius
      (12 * retainedTerminalFanRoutingRefinement - 1)
      center point := by
  rcases List.mem_map.mp pointMember with
    ⟨sourcePoint, sourcePointMember, rfl⟩
  have base :=
    retainedTerminalFanRefinedRoute_points_outside_fan
      direction slot sourcePoint sourcePointMember
  intro translatedBound
  rcases center with ⟨centerX, centerY⟩
  rcases sourcePoint with ⟨sourceX, sourceY⟩
  apply base
  simpa [WithinCoordinateRadius, Cell.add] using translatedBound

/-- Order-compatible positioned routes are strictly separated. -/
theorem retainedTerminalFanRefinedRoutesAt_strictlyAvoidEachOther
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLe :
      firstDirection.angularRank ≤ secondDirection.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanRefinedRouteAt
        center firstDirection firstSlot)
      (retainedTerminalFanRefinedRouteAt
        center secondDirection secondSlot) := by
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther.map_add
      (retainedTerminalFanRefinedRoutes_strictlyAvoidEachOther
        firstDirection secondDirection firstSlot secondSlot
        directionsLe slotsLt)
      center

end PeriodicEightOccurrenceSplit
end LeanTrominoes
