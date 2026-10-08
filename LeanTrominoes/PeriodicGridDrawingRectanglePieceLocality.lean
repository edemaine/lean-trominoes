/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectanglePieceLocalCells
import LeanTrominoes.PeriodicGridDrawingRectanglePieceRawRoutes
import LeanTrominoes.PeriodicGridDrawingStraightRefinementDrawing

/-! # Rectangle routes stay in one of the edge's two endpoint cells -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem liftedRectangleInputRoute_in_refined_cell {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} (columnBound : column < drawing.gridSize) {chord : OrthogonalBoundaryRouting.Chord}
    (member : chord ∈ rectangleChordFamily graph drawing column) (cell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell chord) point) :
    (straightRefinementDrawing graph drawing).RealPointInCell cell point := by
  have bounds := liftedRectangleInputRoute_real_bounds planar degree graphLocal straight member cell contains
  have factorPositive : (0 : ℝ) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  have nonnegative : (0 : ℝ) ≤ crossingBound drawing.gridSize := by positivity
  have columnNonnegative : (0 : ℝ) ≤ column := by positivity
  have columnUpper : (column : ℝ)+1 ≤ drawing.gridSize := by exact_mod_cast (by omega : column+1 ≤ drawing.gridSize)
  simp only [rectangleRouteOffset,paddedSlabOrigin,rectangleRouteIndex,paddedSlabWidth,paddedGridSize] at bounds
  push_cast at bounds
  unfold RealPointInCell
  rw [straightRefinementDrawing_gridSize]
  simp only [paddedGridSize,Nat.cast_mul]
  refine ⟨?_,?_,?_,?_⟩
  all_goals nlinarith [bounds.1,bounds.2.1,bounds.2.2.1,bounds.2.2.2]

theorem rectangleEdgePiece?_isRealLocal {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (column : Nat) (columnBound : column < drawing.gridSize) (cell : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing tagged.2 column cell = some piece)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains piece.route point) :
    (straightRefinementDrawing graph drawing).RealPointInCell (0,0) point ∨
      (straightRefinementDrawing graph drawing).RealPointInCell tagged.1.offset point := by
  cases chord : rectangleParentChord graph drawing column (tagged.2,Cell.scale (-1) cell) with
  | none => simp [rectangleEdgePiece?,chord] at lookup
  | some keys =>
    have cellEq := rectangleParentChord_local_cell planar graphLocal straight member column columnBound cell chord
    have chordMember := rectangleParentChord_mem_family planar.1.1 graphLocal straight column (tagged.2,Cell.scale (-1) cell) chord
    have raw := (rectangleEdgePiece?_raw_image_endpoints tagged.2 column cell lookup chord point).1.mp contains
    have inCell := liftedRectangleInputRoute_in_refined_cell planar degree graphLocal straight columnBound chordMember cell raw
    rcases cellEq with rfl | rfl
    · exact Or.inl inCell
    · exact Or.inr inCell

end LeanTrominoes.PeriodicGridDrawing
