/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleParameterCoverage

/-! # A retained port's parent parameter recovers its exact original position -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem rectanglePort_parameter_point {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    (drawing.liftedStraightSegment key.parentKey.1 key.parentKey.2).rationalPointAtParameter
        (rectanglePortParentParameter graph drawing column key.parentKey key) =
      ((column : ℚ)+columnPerturbation graph drawing+(key.rationalPoint graph drawing column).1,
        -seamPerturbation graph drawing+(key.rationalPoint graph drawing column).2) := by
  let segment := drawing.liftedStraightSegment key.parentKey.1 key.parentKey.2
  let coordinate := (column : ℚ)+columnPerturbation graph drawing+(key.rationalPoint graph drawing column).1
  have spans := rectanglePort_parent_spans_unit_column planar graphLocal straight column valid
  change segment.SpansUnitColumn column at spans
  have nonvertical : segment.start.1 ≠ segment.finish.1 := by rcases spans with forward | backward <;> omega
  have xEqual := GridSegment.rationalXAtParameter_parameter segment coordinate nonvertical
  have height := GridSegment.rationalPointAtParameter_height nonvertical (segment.rationalXParameter coordinate)
  change segment.rationalHeightAt (segment.rationalXAtParameter (segment.rationalXParameter coordinate)) =
    (segment.rationalPointAtParameter (segment.rationalXParameter coordinate)).2 at height
  rw [xEqual] at height
  have contact := rectanglePort_rational_contact planar graphLocal straight column valid
  have affine := rectangle_affine_height graph drawing column key.parentKey (key.rationalPoint graph drawing column).1
  apply Prod.ext
  · exact xEqual
  · change (segment.rationalPointAtParameter (segment.rationalXParameter coordinate)).2 = _
    linarith [contact.1,affine]

def rectanglePortOriginalPoint {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (cell : Cell) (key : RectanglePortKey Vertex) : ℚ × ℚ :=
  ((column : ℚ)+columnPerturbation graph drawing+(key.rationalPoint graph drawing column).1+(drawing.gridSize : ℚ)*cell.1,
    -seamPerturbation graph drawing+(key.rationalPoint graph drawing column).2+(drawing.gridSize : ℚ)*cell.2)

theorem rectanglePort_prototype_parameter_point {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell : Cell) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column)
    (parent : key.parentKey = (index,Cell.scale (-1) cell)) :
    (drawing.liftedStraightSegment index (0,0)).rationalPointAtParameter
        (rectanglePortParentParameter graph drawing column (index,Cell.scale (-1) cell) key) =
      rectanglePortOriginalPoint graph drawing column cell key := by
  have pointEq := rectanglePort_parameter_point planar graphLocal straight column valid
  rw [parent] at pointEq
  have segmentEq : drawing.liftedStraightSegment index (Cell.scale (-1) cell) =
      (drawing.liftedStraightSegment index (0,0)).translate (drawing.periodTranslation (Cell.scale (-1) cell)) := by
    simpa only [Cell.add,zero_add] using liftedStraightSegment_add_cell drawing index (0,0) (Cell.scale (-1) cell)
  rw [segmentEq,GridSegment.rationalPointAtParameter_translate] at pointEq
  have first := congrArg Prod.fst pointEq
  have second := congrArg Prod.snd pointEq
  have shiftX : ((drawing.periodTranslation (Cell.scale (-1) cell)).1 : ℚ) = -(drawing.gridSize : ℚ)*cell.1 := by
    simp [periodTranslation,Cell.scale]
  have shiftY : ((drawing.periodTranslation (Cell.scale (-1) cell)).2 : ℚ) = -(drawing.gridSize : ℚ)*cell.2 := by
    simp [periodTranslation,Cell.scale]
  dsimp only [Prod.fst,Prod.snd] at first second
  rw [shiftX] at first
  rw [shiftY] at second
  apply Prod.ext <;> dsimp only [rectanglePortOriginalPoint]
  · linarith [first]
  · linarith [second]

end LeanTrominoes.PeriodicGridDrawing
