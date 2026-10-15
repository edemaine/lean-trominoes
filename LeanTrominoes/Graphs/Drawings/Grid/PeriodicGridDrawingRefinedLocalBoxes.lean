/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Straight.PeriodicGridDrawingStraightRefinementDrawing
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRealLocalBounds

/-! # Coordinate bounds for the refined local rectangle imply two-cell locality -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem refined_real_local_of_coordinate_box {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) {offset : Cell}
    (localOffset : offset.1.natAbs+offset.2.natAbs ≤ 1) {point : ℝ × ℝ}
    (bounds : (paddedGridSize drawing.gridSize : ℝ)*(min 0 offset.1 : Int) ≤ point.1 ∧
      point.1 ≤ (paddedGridSize drawing.gridSize : ℝ)*((max 0 offset.1 : Int)+1) ∧
      (paddedGridSize drawing.gridSize : ℝ)*(min 0 offset.2 : Int) ≤ point.2 ∧
      point.2 ≤ (paddedGridSize drawing.gridSize : ℝ)*((max 0 offset.2 : Int)+1)) :
    (straightRefinementDrawing graph drawing).RealPointInCell (0,0) point ∨
      (straightRefinementDrawing graph drawing).RealPointInCell offset point := by
  apply real_local_of_rectangle localOffset
  rw [straightRefinementDrawing_gridSize]
  have nonnegative : (0 : Int) ≤ paddedGridSize drawing.gridSize := by positivity
  have minX := (mul_min_of_nonneg (0 : Int) offset.1 nonnegative).symm
  have maxX := (mul_max_of_nonneg (0 : Int) offset.1 nonnegative).symm
  have minY := (mul_min_of_nonneg (0 : Int) offset.2 nonnegative).symm
  have maxY := (mul_max_of_nonneg (0 : Int) offset.2 nonnegative).symm
  simp only [mul_zero] at minX maxX minY maxY
  rw [minX,maxX,minY,maxY]
  push_cast at bounds ⊢
  refine ⟨bounds.1,?_,bounds.2.2.1,?_⟩ <;> nlinarith [bounds.2.1,bounds.2.2.2]

end LeanTrominoes.PeriodicGridDrawing
