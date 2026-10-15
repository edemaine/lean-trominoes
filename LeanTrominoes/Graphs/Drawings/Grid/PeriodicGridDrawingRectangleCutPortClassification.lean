/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleVerticalPortPositions

/-! # Rectangle ports at a cut boundary identify the side and integer line -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalIntegerStripCover

theorem rectanglePort_at_cut_boundary {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) (line : Int) (right : Bool)
    {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column)
    (onCut : (rectanglePortOriginalPoint graph drawing column cell key).1 =
      (line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing)) :
    line = (column : Int)+(if right then 1 else 0)+(drawing.gridSize : Int)*cell.1 ∧
      ∃ raw : ColumnPortKey Vertex, key = .vertical right raw := by
  have positive := columnPerturbation_positive planar straight
  have small := virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
  have bounds := (rectanglePortOriginalPoint_bounds planar graphLocal straight column cell valid).1
  cases right
  · simp only [Bool.false_eq_true,if_false,add_zero] at onCut ⊢
    have candidate : SlabContains (columnPerturbation graph drawing) line
        (rectanglePortOriginalPoint graph drawing column cell key).1 := by
      unfold SlabContains
      rw [onCut]
      constructor <;> linarith
    have columns := closed_slab_column_unique positive bounds candidate
    have castColumns : (column : ℚ)+(drawing.gridSize : ℚ)*cell.1 = line := by
      exact_mod_cast columns
    refine ⟨columns.symm,rectanglePort_vertical_of_left_contact planar graphLocal straight column cell valid ?_⟩
    rw [onCut]
    linarith
  · simp only [if_true] at onCut ⊢
    have candidate : SlabContains (columnPerturbation graph drawing) (line-1)
        (rectanglePortOriginalPoint graph drawing column cell key).1 := by
      unfold SlabContains
      rw [onCut]
      push_cast
      constructor <;> linarith
    have columns := closed_slab_column_unique positive bounds candidate
    have castColumns : (column : ℚ)+(drawing.gridSize : ℚ)*cell.1 = (line : ℚ)-1 := by
      exact_mod_cast columns
    refine ⟨by omega,rectanglePort_vertical_of_right_contact planar graphLocal straight column cell valid ?_⟩
    rw [onCut]
    linarith

end LeanTrominoes.PeriodicGridDrawing
