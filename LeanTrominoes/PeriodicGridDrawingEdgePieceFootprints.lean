/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingEdgePieceColumnCoverage
import LeanTrominoes.PeriodicGridDrawingRectangleOpenParameterBounds

/-! # Interior piece parameters lie in their original disjoint rectangle or cut strip -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalIntegerStripCover

theorem rectangleEdgePiece?_open_footprint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (columnBound : column < drawing.gridSize) (cell : Cell)
    {piece : EdgeRoutePiece} (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    (parameter : ℚ) (after : piece.start < parameter) (before : parameter < piece.finish) :
    SlabInteriorContains (columnPerturbation graph drawing) ((column : Int)+(drawing.gridSize : Int)*cell.1)
        ((drawing.liftedStraightSegment index (0,0)).rationalPointAtParameter parameter).1 ∧
      RowInteriorContains (drawing.gridSize : ℚ) (seamPerturbation graph drawing) cell.2
        ((drawing.liftedStraightSegment index (0,0)).rationalPointAtParameter parameter).2 := by
  unfold rectangleEdgePiece? at lookup
  cases chord : rectangleParentChord graph drawing column (index,Cell.scale (-1) cell) with
  | none => simp [chord] at lookup
  | some keys =>
    have pieceEq := Option.some.inj (by simpa only [chord,Option.map_some] using lookup)
    subst piece
    have bounds := rectangleParentChordInterval_open_bounds planar graphLocal straight column columnBound
      (index,Cell.scale (-1) cell) chord parameter after before
    have segmentEq : drawing.liftedStraightSegment index (Cell.scale (-1) cell) =
        (drawing.liftedStraightSegment index (0,0)).translate (drawing.periodTranslation (Cell.scale (-1) cell)) := by
      simpa only [Cell.add,zero_add] using liftedStraightSegment_add_cell drawing index (0,0) (Cell.scale (-1) cell)
    rw [segmentEq,GridSegment.rationalPointAtParameter_translate] at bounds
    simp only [periodTranslation,Cell.scale] at bounds
    push_cast at bounds
    unfold SlabInteriorContains RowInteriorContains
    push_cast
    exact ⟨⟨by linarith [bounds.1.1],by linarith [bounds.1.2]⟩,
      ⟨by linarith [bounds.2.1],by linarith [bounds.2.2]⟩⟩

theorem crossingEdgePiece_open_footprint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index : Nat) (line : Int) (crosses : (drawing.liftedStraightSegment index (0,0)).CrossesVerticalLine line)
    (parameter : ℚ) (after : (crossingEdgePiece graph drawing index line).start < parameter)
    (before : parameter < (crossingEdgePiece graph drawing index line).finish) :
    CutContains (columnPerturbation graph drawing) line
      ((drawing.liftedStraightSegment index (0,0)).rationalPointAtParameter parameter).1 := by
  have positive := columnPerturbation_positive planar straight
  have nonvertical : (drawing.liftedStraightSegment index (0,0)).start.1 ≠
      (drawing.liftedStraightSegment index (0,0)).finish.1 := by rcases crosses with forward | backward <;> omega
  have parameterEq := GridSegment.rationalXParameter_xAtParameter nonvertical parameter
  have openBetween := (GridSegment.rationalXParameter_between_open_iff nonvertical
    ((line : ℚ)-columnPerturbation graph drawing) ((line : ℚ)+columnPerturbation graph drawing)
    ((drawing.liftedStraightSegment index (0,0)).rationalXAtParameter parameter)).mp
      (by rw [parameterEq]; exact ⟨after,before⟩)
  have order : (line : ℚ)-columnPerturbation graph drawing ≤ (line : ℚ)+columnPerturbation graph drawing := by linarith
  simp only [min_eq_left order,max_eq_right order] at openBetween
  exact ⟨openBetween.1.le,openBetween.2.le⟩

end LeanTrominoes.PeriodicGridDrawing
