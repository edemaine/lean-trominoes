/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePortParameterPoints
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalIntegerStripCover

/-! # Original rectangle ports lie in their closed slab and row, with proper faces -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalAffineBoundary RationalIntegerStripCover

theorem rectanglePortOriginalPoint_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    SlabContains (columnPerturbation graph drawing) ((column : Int)+(drawing.gridSize : Int)*cell.1)
        (rectanglePortOriginalPoint graph drawing column cell key).1 ∧
      RowContains (drawing.gridSize : ℚ) (seamPerturbation graph drawing) cell.2
        (rectanglePortOriginalPoint graph drawing column cell key).2 := by
  have contact := rectanglePort_rational_contact planar graphLocal straight column valid
  have widthPositive := virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
  have heightPositive : (0 : ℚ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have bounds := contact_coordinate_bounds widthPositive heightPositive contact
  unfold SlabContains RowContains rectanglePortOriginalPoint
  push_cast
  exact ⟨⟨by linarith [bounds.1.1],by linarith [bounds.1.2]⟩,
    ⟨by linarith [bounds.2.1],by linarith [bounds.2.2]⟩⟩

theorem rectangle_vertical_original_row_interior {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) (right : Bool) {key : ColumnPortKey Vertex}
    (valid : (RectanglePortKey.vertical right key).Valid graph drawing column) :
    RowInteriorContains (drawing.gridSize : ℚ) (seamPerturbation graph drawing) cell.2
      (rectanglePortOriginalPoint graph drawing column cell (.vertical right key)).2 := by
  have contact := rectanglePort_rational_contact planar graphLocal straight column valid
  have verticalSide : ((RectanglePortKey.vertical right key).rationalPoint graph drawing column).1 = 0 ∨
      ((RectanglePortKey.vertical right key).rationalPoint graph drawing column).1 = 1-2*columnPerturbation graph drawing := by
    cases right <;> simp [RectanglePortKey.rationalPoint,RectanglePortKey.side,boundaryPoint]
  have yInside : 0 < ((RectanglePortKey.vertical right key).rationalPoint graph drawing column).2 ∧
      ((RectanglePortKey.vertical right key).rationalPoint graph drawing column).2 < (drawing.gridSize : ℚ) := by
    rcases contact.2 with vertical | horizontal
    · exact vertical.2
    · rcases verticalSide with left | right <;> linarith [horizontal.2.1,horizontal.2.2]
  unfold RowInteriorContains rectanglePortOriginalPoint
  exact ⟨by linarith [yInside.1],by linarith [yInside.2]⟩

theorem rectangle_horizontal_original_point_y {Vertex : Type*}
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) (cell : Cell) (top : Bool) (key : Nat × Cell) :
    (rectanglePortOriginalPoint graph drawing column cell (.horizontal top key)).2 =
      (drawing.gridSize : ℚ)*((cell.2 : ℚ)+(if top then 1 else 0))-seamPerturbation graph drawing := by
  cases top <;> simp [rectanglePortOriginalPoint,RectanglePortKey.rationalPoint,RectanglePortKey.side,boundaryPoint] <;> ring

theorem rectanglePort_horizontal_of_bottom_contact {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column)
    (onBottom : (rectanglePortOriginalPoint graph drawing column cell key).2 =
      (drawing.gridSize : ℚ)*cell.2-seamPerturbation graph drawing) :
    ∃ raw : Nat × Cell, key = .horizontal false raw := by
  cases key with
  | vertical right raw =>
    have inside := rectangle_vertical_original_row_interior planar graphLocal straight column cell right valid
    rw [onBottom] at inside
    exact (lt_irrefl _ inside.1).elim
  | horizontal top raw =>
    cases top
    · exact ⟨raw,rfl⟩
    · rw [rectangle_horizontal_original_point_y] at onBottom
      have positive : (0 : ℚ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
      simp only [if_true] at onBottom
      linarith

theorem rectanglePort_horizontal_of_top_contact {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column)
    (onTop : (rectanglePortOriginalPoint graph drawing column cell key).2 =
      (drawing.gridSize : ℚ)*((cell.2 : ℚ)+1)-seamPerturbation graph drawing) :
    ∃ raw : Nat × Cell, key = .horizontal true raw := by
  cases key with
  | vertical right raw =>
    have inside := rectangle_vertical_original_row_interior planar graphLocal straight column cell right valid
    rw [onTop] at inside
    exact (lt_irrefl _ inside.2).elim
  | horizontal top raw =>
    cases top
    · rw [rectangle_horizontal_original_point_y] at onTop
      have positive : (0 : ℚ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
      simp only [Bool.false_eq_true,if_false,add_zero] at onTop
      linarith
    · exact ⟨raw,rfl⟩

end LeanTrominoes.PeriodicGridDrawing
