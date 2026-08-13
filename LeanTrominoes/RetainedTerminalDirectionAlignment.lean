/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedTerminalSplicePoint

/-!
# Axis alignment of classified terminal directions

Terminal classification records a positive multiple of one primitive ray.
Consequently two terminal segments with the same classified direction are
either both axis-aligned or both oblique.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree
open OccurrenceSplitRing
open PlanarThreeSAT

set_option maxHeartbeats 2000000

/-- Two nondegenerate segments with successful retained classifications but
different axis-alignment status have different classified directions. -/
theorem retainedTerminalDirections_ne_of_segment_alignment_ne
    {firstStart firstFinish secondStart secondFinish : Cell}
    {firstDirection secondDirection : RetainedTerminalDirection}
    {firstLength secondLength : Nat}
    (firstClassified :
      retainedTerminalDirectionClassify
          (Cell.sub firstStart firstFinish) =
        some (firstDirection, firstLength))
    (secondClassified :
      retainedTerminalDirectionClassify
          (Cell.sub secondStart secondFinish) =
        some (secondDirection, secondLength))
    (firstAligned :
      (GridSegment.mk firstStart firstFinish).IsAxisAligned)
    (secondNotAligned :
      ¬(GridSegment.mk secondStart secondFinish).IsAxisAligned) :
    firstDirection ≠ secondDirection := by
  intro directionsEqual
  subst secondDirection
  have firstSound :=
    retainedTerminalDirectionClassify_sound firstClassified
  have secondSound :=
    retainedTerminalDirectionClassify_sound secondClassified
  rcases firstStart with ⟨firstStartX, firstStartY⟩
  rcases firstFinish with ⟨firstFinishX, firstFinishY⟩
  rcases secondStart with ⟨secondStartX, secondStartY⟩
  rcases secondFinish with ⟨secondFinishX, secondFinishY⟩
  cases firstDirection with
  | compass port =>
      cases port <;>
        simp_all [GridSegment.IsAxisAligned,
          GridSegment.IsHorizontal, GridSegment.IsVertical,
          RetainedTerminalDirection.primitive, Port.unitVector,
          Cell.sub, Cell.scale] <;>
        omega
  | routedClause arm =>
      cases arm <;>
        simp_all [GridSegment.IsAxisAligned,
          GridSegment.IsHorizontal, GridSegment.IsVertical,
          RetainedTerminalDirection.primitive,
          routedClauseRayPrimitive,
          Cell.sub, Cell.scale] <;>
        omega

/-- For routes with genuine final segments, differing axis-alignment status
forces their classified retained terminal directions to differ. -/
theorem retainedTerminalDirections_ne_of_finalSegment_alignment_ne
    {firstRoute secondRoute : List Cell}
    {firstDirection secondDirection : RetainedTerminalDirection}
    {firstLength secondLength : Nat}
    (firstRouteLength : 2 ≤ firstRoute.length)
    (secondRouteLength : 2 ≤ secondRoute.length)
    (firstClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector firstRoute) =
        some (firstDirection, firstLength))
    (secondClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector secondRoute) =
        some (secondDirection, secondLength))
    (firstAligned :
      (GridSegment.mk
        (polylineLastEntrance firstRoute)
        (firstRoute.getLastD (0, 0))).IsAxisAligned)
    (secondNotAligned :
      ¬(GridSegment.mk
        (polylineLastEntrance secondRoute)
        (secondRoute.getLastD (0, 0))).IsAxisAligned) :
    firstDirection ≠ secondDirection := by
  rw [routeTerminalVector_eq_sub_lastEntrance
      firstRoute firstRouteLength] at firstClassified
  rw [routeTerminalVector_eq_sub_lastEntrance
      secondRoute secondRouteLength] at secondClassified
  exact retainedTerminalDirections_ne_of_segment_alignment_ne
    firstClassified secondClassified firstAligned secondNotAligned

end PeriodicEightOccurrenceSplit
end LeanTrominoes
