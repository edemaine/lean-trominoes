/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingColumnPerturbation
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVirtualHorizontalPorts

/-! # Column-cut intersections are proper ports of the virtual rectangles -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalPerturbation RealRectangleBoundary

def perturbedColumnHeight {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (key : Nat × Cell) (right : Bool) : ℚ :=
  (drawing.liftedStraightSegment key.1 key.2).rationalHeightAt
    ((line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing))

theorem perturbedColumnHeight_eq_evaluate {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (key : Nat × Cell) (right : Bool) :
    perturbedColumnHeight graph drawing line key right = evaluate (columnPerturbation graph drawing)
      ((drawing.liftedStraightSegment key.1 key.2).rationalLineHeight line,
        if right then -(drawing.liftedStraightSegment key.1 key.2).rationalSlope else
          (drawing.liftedStraightSegment key.1 key.2).rationalSlope) := by
  unfold perturbedColumnHeight
  rw [GridSegment.rationalHeightAt_add,GridSegment.rationalHeightAt_int]
  cases right <;> simp [evaluate] <;> ring

theorem columnPerturbation_abs_small {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) (right : Bool) :
    |if right then -columnPerturbation graph drawing else columnPerturbation graph drawing| < 1 := by
  have positive := columnPerturbation_positive planar straight
  have small := (columnPerturbation_le_cutMargin planar straight).trans_lt (columnCutMargin_lt_half graph drawing)
  have absolute : |columnPerturbation graph drawing| < 1 := by rw [abs_of_pos positive]; linarith
  cases right <;> simpa using absolute

theorem perturbedColumnHeight_in_row {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} (columnBound : column < drawing.gridSize) {key : Nat × Cell}
    (member : key ∈ verticalCrossingCopies graph drawing column) (right : Bool) :
    -seamPerturbation graph drawing < perturbedColumnHeight graph drawing column key right ∧
      perturbedColumnHeight graph drawing column key right < (drawing.gridSize : ℚ)-seamPerturbation graph drawing := by
  have data := of_decide_eq_true (List.mem_filter.mp member).2
  have shiftPositive := seamPerturbation_positive graph drawing
  have gap := seamPerturbation_below_row_gap columnBound member
  have lowerOld : -seamPerturbation graph drawing < (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column := by linarith [data.2.1]
  have upperOld : (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column < (drawing.gridSize : ℚ)-seamPerturbation graph drawing := by linarith
  have pointMember := mem_columnPerturbationValues_crossing columnBound member right
  have rows := mem_columnPerturbationValues_rows graph drawing
  have lo := columnPerturbation_preserves_order planar straight rows.1 pointMember (Or.inl lowerOld)
  have hi := columnPerturbation_preserves_order planar straight pointMember rows.2 (Or.inl upperOld)
  rw [perturbedColumnHeight_eq_evaluate]
  constructor
  · simpa only [evaluate,Prod.fst,Prod.snd,mul_zero,add_zero] using lo
  · simpa only [evaluate,Prod.fst,Prod.snd,mul_zero,add_zero] using hi

theorem perturbedColumnHeight_realInteriorContains {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (line : Int) (key : Nat × Cell) (crosses : (drawing.liftedStraightSegment key.1 key.2).CrossesVerticalLine line) (right : Bool) :
    (drawing.liftedStraightSegment key.1 key.2).RealInteriorContains
      (((line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing) : ℝ),
        (perturbedColumnHeight graph drawing line key right : ℝ)) := by
  simpa only [perturbedColumnHeight,Rat.cast_add,Rat.cast_intCast] using
    GridSegment.shifted_vertical_cut_realInteriorContains crosses (columnPerturbation_abs_small planar straight right)

def virtualVerticalPort {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (key : Nat × Cell) (right : Bool) : Port :=
  ⟨if right then 2 else 0,((perturbedColumnHeight graph drawing line key right+seamPerturbation graph drawing) : ℝ)⟩

theorem virtualVerticalPort_inside {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} (columnBound : column < drawing.gridSize) {key : Nat × Cell}
    (member : key ∈ verticalCrossingCopies graph drawing column) (right : Bool) :
    (virtualVerticalPort graph drawing column key right).Inside
      ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ) := by
  have bounds := perturbedColumnHeight_in_row planar straight columnBound member right
  have lo : (0 : ℚ) < perturbedColumnHeight graph drawing column key right+seamPerturbation graph drawing := by linarith
  have hi : perturbedColumnHeight graph drawing column key right+seamPerturbation graph drawing < (drawing.gridSize : ℚ) := by linarith
  have realBounds : (0 : ℝ) < ((perturbedColumnHeight graph drawing column key right+seamPerturbation graph drawing) : ℝ) ∧
      ((perturbedColumnHeight graph drawing column key right+seamPerturbation graph drawing) : ℝ) < (drawing.gridSize : ℝ) :=
    ⟨by exact_mod_cast lo,by exact_mod_cast hi⟩
  cases right <;> simpa [virtualVerticalPort,Port.Inside,Port.extent] using realBounds

theorem virtualVerticalPort_point {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (key : Nat × Cell) (right : Bool) :
    (virtualVerticalPort graph drawing line key right).shiftedPoint
      (virtualSlabOrigin graph drawing (columnPerturbation graph drawing) (line-if right then 1 else 0) 0)
      ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ) =
    (((line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing) : ℝ),
      (perturbedColumnHeight graph drawing line key right : ℝ)) := by
  cases right <;> apply Prod.ext <;>
    simp [virtualVerticalPort,virtualSlabOrigin,Port.shiftedPoint,Port.point] <;> ring

end LeanTrominoes.PeriodicGridDrawing
