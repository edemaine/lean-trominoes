/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleClipIntervals
import LeanTrominoes.GridSegmentRationalXParameter
import LeanTrominoes.RationalIntervalPartition

/-! # Actual rectangle clips have positive parameter intervals inside their parent edge -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalAffineBoundary RationalIntervalPartition

def rectanglePortParentParameter {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) (key : RectanglePortKey Vertex) : ℚ :=
  (drawing.liftedStraightSegment parent.1 parent.2).rationalXParameter
    ((column : ℚ)+columnPerturbation graph drawing+(key.rationalPoint graph drawing column).1)

theorem rectangleParentChord_parameter_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (parent : Nat × Cell) {first last : RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some (first,last)) :
    (0 < rectanglePortParentParameter graph drawing column parent first ∧ rectanglePortParentParameter graph drawing column parent first < 1) ∧
      (0 < rectanglePortParentParameter graph drawing column parent last ∧ rectanglePortParentParameter graph drawing column parent last < 1) ∧
      rectanglePortParentParameter graph drawing column parent first ≠ rectanglePortParentParameter graph drawing column parent last := by
  have data := rectangleParentChord_data graph drawing column parent lookup
  have spans := rectanglePort_parent_spans_unit_column planar graphLocal straight column data.1
  rw [data.2.2.1] at spans
  have nonvertical : (drawing.liftedStraightSegment parent.1 parent.2).start.1 ≠ (drawing.liftedStraightSegment parent.1 parent.2).finish.1 := by
    intro equal
    rcases spans with forward | backward <;> omega
  have firstContact := rectanglePort_rational_contact planar graphLocal straight column data.1
  have lastContact := rectanglePort_rational_contact planar graphLocal straight column data.2.1
  have widthPositive := virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
  have heightPositive : (0 : ℚ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have firstBounds := (contact_coordinate_bounds widthPositive heightPositive firstContact).1
  have lastBounds := (contact_coordinate_bounds widthPositive heightPositive lastContact).1
  have firstBetween := GridSegment.unit_column_inner_coordinate_between spans (columnPerturbation_positive planar straight) firstBounds
  have lastBetween := GridSegment.unit_column_inner_coordinate_between spans (columnPerturbation_positive planar straight) lastBounds
  refine ⟨?_,?_,?_⟩
  · simpa only [rectanglePortParentParameter,Int.cast_natCast] using GridSegment.rationalXParameter_in_unit_interval firstBetween
  · simpa only [rectanglePortParentParameter,Int.cast_natCast] using GridSegment.rationalXParameter_in_unit_interval lastBetween
  · intro equal
    have coordinatesEqual := GridSegment.rationalXParameter_injective nonvertical equal
    have different := rectangleParentChord_x_distinct planar graphLocal straight column parent lookup
    apply different
    linarith

def rectangleParentChordInterval {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (parent : Nat × Cell) {first last : RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some (first,last)) : Interval where
  start := min (rectanglePortParentParameter graph drawing column parent first) (rectanglePortParentParameter graph drawing column parent last)
  finish := max (rectanglePortParentParameter graph drawing column parent first) (rectanglePortParentParameter graph drawing column parent last)
  positive := by
    have different := (rectangleParentChord_parameter_bounds planar graphLocal straight column parent lookup).2.2
    rcases lt_or_gt_of_ne different with before | after
    · simpa only [min_eq_left before.le,max_eq_right before.le] using before
    · simpa only [min_eq_right after.le,max_eq_left after.le] using after

theorem rectangleParentChordInterval_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (parent : Nat × Cell) {first last : RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some (first,last)) :
    0 < (rectangleParentChordInterval planar graphLocal straight column parent lookup).start ∧
      (rectangleParentChordInterval planar graphLocal straight column parent lookup).finish < 1 := by
  have bounds := rectangleParentChord_parameter_bounds planar graphLocal straight column parent lookup
  exact ⟨lt_min bounds.1.1 bounds.2.1.1,max_lt bounds.1.2 bounds.2.1.2⟩

end LeanTrominoes.PeriodicGridDrawing
