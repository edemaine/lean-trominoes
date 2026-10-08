/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleParameterIntervals
import LeanTrominoes.GridSegmentRationalXParameterOrder

/-! # Parameter intervals cover exactly the original affine rectangle clips -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalAffineBoundary RationalIntervalPartition

theorem rectangleParentChordInterval_contains_iff {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (columnBound : column < drawing.gridSize) (parent : Nat × Cell)
    {first last : RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some (first,last)) {point : ℚ × ℚ}
    (onLine : point.2 = rectangleAffineBase graph drawing column parent+
      (drawing.liftedStraightSegment parent.1 parent.2).rationalSlope*point.1) :
    (rectangleParentChordInterval planar graphLocal straight column parent lookup).Contains
      ((drawing.liftedStraightSegment parent.1 parent.2).rationalXParameter
        ((column : ℚ)+columnPerturbation graph drawing+point.1)) ↔
      ClosedPoint (1-2*columnPerturbation graph drawing) drawing.gridSize (rectangleAffineBase graph drawing column parent)
        (drawing.liftedStraightSegment parent.1 parent.2).rationalSlope point := by
  have data := rectangleParentChord_data graph drawing column parent lookup
  have spans := rectanglePort_parent_spans_unit_column planar graphLocal straight column data.1
  rw [data.2.2.1] at spans
  have nonvertical : (drawing.liftedStraightSegment parent.1 parent.2).start.1 ≠
      (drawing.liftedStraightSegment parent.1 parent.2).finish.1 := by rcases spans with forward | backward <;> omega
  have parameterBetween := GridSegment.rationalXParameter_between_iff nonvertical
    ((column : ℚ)+columnPerturbation graph drawing+(first.rationalPoint graph drawing column).1)
    ((column : ℚ)+columnPerturbation graph drawing+(last.rationalPoint graph drawing column).1)
    ((column : ℚ)+columnPerturbation graph drawing+point.1)
  have unshifted : (rectangleParentChordInterval planar graphLocal straight column parent lookup).Contains
      ((drawing.liftedStraightSegment parent.1 parent.2).rationalXParameter
        ((column : ℚ)+columnPerturbation graph drawing+point.1)) ↔
      min (first.rationalPoint graph drawing column).1 (last.rationalPoint graph drawing column).1 ≤ point.1 ∧
        point.1 ≤ max (first.rationalPoint graph drawing column).1 (last.rationalPoint graph drawing column).1 := by
    simpa only [Interval.Contains,rectangleParentChordInterval,rectanglePortParentParameter,
      min_le_iff,le_max_iff,add_le_add_iff_left] using parameterBetween
  exact unshifted.trans (rectangleParentChord_clip_interval planar graphLocal straight column columnBound parent lookup onLine).symm

end LeanTrominoes.PeriodicGridDrawing
