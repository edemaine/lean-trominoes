/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingStraightSegments
import LeanTrominoes.GridSegmentRationalVerticalCrossing

/-! # Planarity separates exact rational crossing heights -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem vertical_crossing_heights_ne {drawing : PeriodicGridDrawing}
    (planar : drawing.RealRoutesMeetOnlyAtEndpoints) {firstIndex secondIndex : Nat}
    (firstValid : firstIndex < drawing.edgeRoutes.length) (secondValid : secondIndex < drawing.edgeRoutes.length)
    (firstStraight : (drawing.edgeRoute firstIndex).length = 2) (secondStraight : (drawing.edgeRoute secondIndex).length = 2)
    (firstCell secondCell : Cell) (different : (firstIndex,firstCell) ≠ (secondIndex,secondCell)) {line : Int}
    (firstCrosses : (drawing.liftedStraightSegment firstIndex firstCell).CrossesVerticalLine line)
    (secondCrosses : (drawing.liftedStraightSegment secondIndex secondCell).CrossesVerticalLine line) :
    (drawing.liftedStraightSegment firstIndex firstCell).rationalLineHeight line ≠
      (drawing.liftedStraightSegment secondIndex secondCell).rationalLineHeight line := by
  intro equal
  have firstContains := GridSegment.rationalLineHeight_realContains firstCrosses
  have secondContains := GridSegment.rationalLineHeight_realContains secondCrosses
  rw [← equal] at secondContains
  have endpoint := (planar firstIndex secondIndex firstCell secondCell firstValid secondValid different _
    ((realEdgeRoute_straight_image drawing firstIndex firstCell firstStraight _).mpr firstContains)
    ((realEdgeRoute_straight_image drawing secondIndex secondCell secondStraight _).mpr secondContains)).1
  have avoids := GridSegment.rationalLineHeight_not_endpoint firstCrosses
  rcases (realEdgeRoute_straight_endpoints drawing firstIndex firstCell firstStraight _).mp endpoint with start | finish
  · exact avoids.1 start
  · exact avoids.2 finish

end LeanTrominoes.PeriodicGridDrawing
