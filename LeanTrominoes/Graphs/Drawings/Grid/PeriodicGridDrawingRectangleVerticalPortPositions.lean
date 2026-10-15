/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleOriginalPortBounds

/-! # Original vertical rectangle ports identify their integer cut line exactly -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalAffineBoundary RationalIntegerStripCover

theorem rectangle_vertical_original_point_x {Vertex : Type*}
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) (cell : Cell) (right : Bool) (key : ColumnPortKey Vertex) :
    (rectanglePortOriginalPoint graph drawing column cell (.vertical right key)).1 =
      (column : ℚ)+(if right then 1 else 0)+(drawing.gridSize : ℚ)*cell.1+
        (if right then -columnPerturbation graph drawing else columnPerturbation graph drawing) := by
  cases right <;> simp [rectanglePortOriginalPoint,RectanglePortKey.rationalPoint,RectanglePortKey.side,boundaryPoint] <;> ring

theorem rectangle_horizontal_original_slab_interior {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) (top : Bool) {key : Nat × Cell}
    (valid : (RectanglePortKey.horizontal top key).Valid graph drawing column) :
    SlabInteriorContains (columnPerturbation graph drawing) ((column : Int)+(drawing.gridSize : Int)*cell.1)
      (rectanglePortOriginalPoint graph drawing column cell (.horizontal top key)).1 := by
  have contact := rectanglePort_rational_contact planar graphLocal straight column valid
  have horizontalSide : ((RectanglePortKey.horizontal top key).rationalPoint graph drawing column).2 = 0 ∨
      ((RectanglePortKey.horizontal top key).rationalPoint graph drawing column).2 = (drawing.gridSize : ℚ) := by
    cases top <;> simp [RectanglePortKey.rationalPoint,RectanglePortKey.side,boundaryPoint]
  have xInside : 0 < ((RectanglePortKey.horizontal top key).rationalPoint graph drawing column).1 ∧
      ((RectanglePortKey.horizontal top key).rationalPoint graph drawing column).1 < 1-2*columnPerturbation graph drawing := by
    rcases contact.2 with vertical | horizontal
    · rcases horizontalSide with bottom | top <;> linarith [vertical.2.1,vertical.2.2]
    · exact horizontal.2
  unfold SlabInteriorContains rectanglePortOriginalPoint
  push_cast
  exact ⟨by linarith [xInside.1],by linarith [xInside.2]⟩

theorem rectanglePort_vertical_of_left_contact {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column)
    (onLeft : (rectanglePortOriginalPoint graph drawing column cell key).1 =
      (column : ℚ)+columnPerturbation graph drawing+(drawing.gridSize : ℚ)*cell.1) :
    ∃ raw : ColumnPortKey Vertex, key = .vertical false raw := by
  have widthPositive := virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
  cases key with
  | vertical right raw =>
    cases right
    · exact ⟨raw,rfl⟩
    · rw [rectangle_vertical_original_point_x] at onLeft
      simp only [if_true] at onLeft
      linarith
  | horizontal top raw =>
    have interior := rectangle_horizontal_original_slab_interior planar graphLocal straight column cell top valid
    unfold SlabInteriorContains at interior
    push_cast at interior
    rw [onLeft] at interior
    linarith [interior.1]

theorem rectanglePort_vertical_of_right_contact {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column)
    (onRight : (rectanglePortOriginalPoint graph drawing column cell key).1 =
      (column : ℚ)+1-columnPerturbation graph drawing+(drawing.gridSize : ℚ)*cell.1) :
    ∃ raw : ColumnPortKey Vertex, key = .vertical true raw := by
  have widthPositive := virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
  cases key with
  | vertical right raw =>
    cases right
    · rw [rectangle_vertical_original_point_x] at onRight
      simp only [Bool.false_eq_true,if_false,add_zero] at onRight
      linarith
    · exact ⟨raw,rfl⟩
  | horizontal top raw =>
    have interior := rectangle_horizontal_original_slab_interior planar graphLocal straight column cell top valid
    unfold SlabInteriorContains at interior
    push_cast at interior
    rw [onRight] at interior
    linarith [interior.2]

end LeanTrominoes.PeriodicGridDrawing
