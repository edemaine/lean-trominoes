/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendCellLocality

/-! # Bounds on polygonal bends and segment directions -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem pointInLocalRectangle_of_realCell_in_cell {drawing : PeriodicGridDrawing}
    {offset p : Cell}
    (inside : drawing.RealPointInCell (0,0) (realCell p) ∨
      drawing.RealPointInCell offset (realCell p)) :
    drawing.PointInLocalRectangle offset p := by
  have bounds : (0≤p.1 ∧ p.1≤(drawing.gridSize:Int) ∧ 0≤p.2 ∧ p.2≤(drawing.gridSize:Int)) ∨
      ((drawing.gridSize:Int)*offset.1≤p.1 ∧ p.1≤(drawing.gridSize:Int)*(offset.1+1) ∧
        (drawing.gridSize:Int)*offset.2≤p.2 ∧ p.2≤(drawing.gridSize:Int)*(offset.2+1)) := by
    rcases inside with inside | inside
    · left
      simp [RealPointInCell,realCell] at inside
      exact_mod_cast inside
    · right
      simp only [RealPointInCell,realCell] at inside
      exact_mod_cast inside
  unfold PointInLocalRectangle
  rcases bounds with bounds | bounds
  · exact ⟨le_trans (min_le_left _ _) bounds.1,
      le_trans bounds.2.1 (by have := le_max_left 0 ((drawing.gridSize:Int)*offset.1); omega),
      le_trans (min_le_left _ _) bounds.2.2.1,
      le_trans bounds.2.2.2 (by have := le_max_left 0 ((drawing.gridSize:Int)*offset.2); omega)⟩
  · refine ⟨le_trans (min_le_right _ _) bounds.1,?_,
      le_trans (min_le_right _ _) bounds.2.2.1,?_⟩
    · have := le_max_right 0 ((drawing.gridSize:Int)*offset.1)
      nlinarith [bounds.2.1]
    · have := le_max_right 0 ((drawing.gridSize:Int)*offset.2)
      nlinarith [bounds.2.2.2]

theorem polygonal_point_in_local_rectangle {Vertex : Type*} {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (localDrawing : drawing.IsRealLocal graph)
    {tagged : PeriodicEdge Vertex × Nat} (edgeMember : tagged∈graph.edges.zipIdx)
    (length : 2≤(drawing.edgeRoute tagged.2).length) {p : Cell}
    (pointMember : p∈drawing.edgeRoute tagged.2) :
    drawing.PointInLocalRectangle tagged.1.offset p := by
  obtain ⟨segment,member,endpoint⟩ := exists_gridPolylineSegment_of_mem length pointMember
  apply pointInLocalRectangle_of_realCell_in_cell
  apply localDrawing tagged edgeMember
  refine ⟨segment,member,?_⟩
  rcases endpoint with rfl | rfl
  · exact GridSegment.realContains_start segment
  · exact GridSegment.realContains_finish segment

theorem local_rectangle_coordinate_difference {drawing : PeriodicGridDrawing} {offset p q : Cell}
    (localOffset : offset.1.natAbs+offset.2.natAbs≤1)
    (firstBounds : drawing.PointInLocalRectangle offset p)
    (secondBounds : drawing.PointInLocalRectangle offset q) :
    |q.1-p.1|≤2*(drawing.gridSize:Int) ∧ |q.2-p.2|≤2*(drawing.gridSize:Int) := by
  have positive : (0:Int)<drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have offsets := PeriodicOrthocrossing.offset_eq_of_span_le_one (⟨(),(),offset⟩ : PeriodicEdge Unit) localOffset
  rcases offsets with rfl | rfl | rfl | rfl | rfl <;>
    simp [PointInLocalRectangle,positive.le] at firstBounds secondBounds <;>
    constructor <;> rw [abs_le] <;> constructor <;> nlinarith

end LeanTrominoes.PeriodicGridDrawing
