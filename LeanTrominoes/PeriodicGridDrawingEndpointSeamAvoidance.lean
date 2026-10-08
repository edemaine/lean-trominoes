/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingLocalSeamBounds

/-! # Lifted prototype endpoints avoid every integer period row seam -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem fundamental_position_avoids_row_seam {drawing : PeriodicGridDrawing} {position : Cell}
    (bounds : drawing.PositionInFundamentalSquare position) (shift row : Int) :
    position.2+(drawing.gridSize : Int)*shift ≠ (drawing.gridSize : Int)*row := by
  have gridPositive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  intro equal
  rcases (show row ≤ shift ∨ shift+1 ≤ row by omega) with before | after
  · have scaled := mul_le_mul_of_nonneg_left before gridPositive.le
    nlinarith [bounds.2.2.1]
  · have scaled := mul_le_mul_of_nonneg_left after gridPositive.le
    nlinarith [bounds.2.2.2]

theorem straight_lifted_endpoints_avoid_row_seam {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (cell : Cell) (row : Int) :
    (drawing.liftedStraightSegment tagged.2 cell).start.2 ≠ (drawing.gridSize : Int)*row ∧
      (drawing.liftedStraightSegment tagged.2 cell).finish.2 ≠ (drawing.gridSize : Int)*row := by
  have endpoints := compatible.1.2 tagged.1 (List.fst_mem_of_mem_zipIdx member)
  have sourceBounds := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem endpoints.1)
  have targetBounds := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem endpoints.2)
  rw [straight_lifted_segment_endpoints compatible member straight cell]
  simpa only [Cell.add,Cell.scale] using And.intro
    (fundamental_position_avoids_row_seam sourceBounds cell.2 row)
    (fundamental_position_avoids_row_seam targetBounds (cell.2+tagged.1.offset.2) row)

theorem straight_local_row_seam_point_x_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) (row : Int)
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine ((drawing.gridSize : Int)*row))
    {point : ℝ × ℝ} (contains : (drawing.liftedStraightSegment tagged.2 cell).RealContains point) :
    (drawing.gridSize : ℝ)*cell.1 < point.1 ∧ point.1 < (drawing.gridSize : ℝ)*(cell.1+1) := by
  have offsetZero := (straight_local_row_seam_bounds compatible member straight edgeLocal cell row crosses).1
  have endpoints := compatible.1.2 tagged.1 (List.fst_mem_of_mem_zipIdx member)
  have sourceBounds := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem endpoints.1)
  have targetBounds := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem endpoints.2)
  have box := GridSegment.realBoxContains_of_realContains contains
  rw [straight_lifted_segment_endpoints compatible member straight cell] at box
  simp only [GridSegment.RealBoxContains,Cell.add,Cell.scale,offsetZero,add_zero] at box
  have lower : (drawing.gridSize : Int)*cell.1 < min
      ((drawing.vertexPosition graph tagged.1.source).1+(drawing.gridSize : Int)*cell.1)
      ((drawing.vertexPosition graph tagged.1.target).1+(drawing.gridSize : Int)*cell.1) := by
    apply lt_min
    · linarith [sourceBounds.1]
    · linarith [targetBounds.1]
  have upper : max
      ((drawing.vertexPosition graph tagged.1.source).1+(drawing.gridSize : Int)*cell.1)
      ((drawing.vertexPosition graph tagged.1.target).1+(drawing.gridSize : Int)*cell.1) <
      (drawing.gridSize : Int)*(cell.1+1) := by
    apply max_lt <;> nlinarith [sourceBounds.2.1,targetBounds.2.1]
  have lowerReal : (drawing.gridSize : ℝ)*cell.1 <
      ((min ((drawing.vertexPosition graph tagged.1.source).1+(drawing.gridSize : Int)*cell.1)
        ((drawing.vertexPosition graph tagged.1.target).1+(drawing.gridSize : Int)*cell.1) : Int) : ℝ) := by exact_mod_cast lower
  have upperReal : ((max ((drawing.vertexPosition graph tagged.1.source).1+(drawing.gridSize : Int)*cell.1)
      ((drawing.vertexPosition graph tagged.1.target).1+(drawing.gridSize : Int)*cell.1) : Int) : ℝ) <
      (drawing.gridSize : ℝ)*(cell.1+1) := by exact_mod_cast upper
  exact ⟨lowerReal.trans_le box.1,box.2.1.trans_lt upperReal⟩

theorem straight_local_row_seam_cell_x_zero {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) (row : Int)
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine ((drawing.gridSize : Int)*row))
    {point : ℝ × ℝ} (contains : (drawing.liftedStraightSegment tagged.2 cell).RealContains point)
    (inside : 0 < point.1 ∧ point.1 < drawing.gridSize) : cell.1 = 0 := by
  have bounds := straight_local_row_seam_point_x_bounds compatible member straight edgeLocal cell row crosses contains
  have gridPositive : (0 : ℝ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  by_contra different
  rcases lt_or_gt_of_ne different with negative | positiveCell
  · have step : (cell.1 : ℝ)+1 ≤ 0 := by exact_mod_cast (by omega : cell.1+1 ≤ 0)
    nlinarith [bounds.2,inside.1]
  · have step : (1 : ℝ) ≤ cell.1 := by exact_mod_cast (by omega : 1 ≤ cell.1)
    nlinarith [bounds.1,inside.2]

end LeanTrominoes.PeriodicGridDrawing
