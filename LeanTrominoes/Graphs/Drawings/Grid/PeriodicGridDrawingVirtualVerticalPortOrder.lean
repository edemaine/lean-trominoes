/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVirtualIncidencePorts
import LeanTrominoes.Graphs.Drawings.Grid.FiniteRationalPerturbationOrder
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalBoundaryPortOrder

/-! # Virtual column crossing ports preserve the integral boundary order -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement RationalPerturbation

theorem columnPerturbation_order_iff {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first second : ℚ × ℚ} (firstMember : first ∈ columnPerturbationValues graph drawing)
    (secondMember : second ∈ columnPerturbationValues graph drawing) :
    evaluate (columnPerturbation graph drawing) first < evaluate (columnPerturbation graph drawing) second ↔
      RationalPerturbation.Before first second :=
  evaluate_lt_iff (columnPerturbation_positive planar straight) (columnPerturbation_le_margin planar straight) firstMember secondMember

theorem perturbedColumnHeights_lt_iff {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} (columnBound : column < drawing.gridSize) {first second : Nat × Cell}
    (firstMember : first ∈ verticalCrossingCopies graph drawing column)
    (secondMember : second ∈ verticalCrossingCopies graph drawing column) (right : Bool) :
    perturbedColumnHeight graph drawing column first right < perturbedColumnHeight graph drawing column second right ↔
      (drawing.liftedStraightSegment first.1 first.2).rationalLineHeight column <
        (drawing.liftedStraightSegment second.1 second.2).rationalLineHeight column := by
  have firstAt := mem_columnPerturbationValues_crossing columnBound firstMember right
  have secondAt := mem_columnPerturbationValues_crossing columnBound secondMember right
  constructor
  · intro ordered
    by_contra wrong
    rcases lt_or_eq_of_le (le_of_not_gt wrong) with reverse | equal
    · have reversed := columnPerturbation_preserves_order planar straight secondAt firstAt (Or.inl reverse)
      rw [← perturbedColumnHeight_eq_evaluate,← perturbedColumnHeight_eq_evaluate] at reversed
      exact lt_asymm ordered reversed
    · have keys := verticalCrossingCopies_height_injective planar straight column firstMember secondMember equal.symm
      subst second
      exact lt_irrefl _ ordered
  · intro ordered
    rw [perturbedColumnHeight_eq_evaluate,perturbedColumnHeight_eq_evaluate]
    exact columnPerturbation_preserves_order planar straight firstAt secondAt (Or.inl ordered)

def finiteVerticalSlabPort {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (key : Nat × Cell) (right : Bool) : OrthogonalBoundaryRouting.Port :=
  ⟨if right then 2 else 0,paddedCrossingHeight graph drawing line
    ((drawing.liftedStraightSegment key.1 key.2).rationalLineHeight line)⟩

theorem virtualVerticalPort_coordinate_order {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} (columnBound : column < drawing.gridSize) {first second : Nat × Cell}
    (firstMember : first ∈ verticalCrossingCopies graph drawing column)
    (secondMember : second ∈ verticalCrossingCopies graph drawing column) (right : Bool)
    (ordered : (virtualVerticalPort graph drawing column first right).coordinate <
      (virtualVerticalPort graph drawing column second right).coordinate) :
    (finiteVerticalSlabPort graph drawing column first right).coordinate <
      (finiteVerticalSlabPort graph drawing column second right).coordinate := by
  have shiftedOrder : perturbedColumnHeight graph drawing column first right < perturbedColumnHeight graph drawing column second right := by
    have realOrder : (perturbedColumnHeight graph drawing column first right : ℝ) <
        (perturbedColumnHeight graph drawing column second right : ℝ) := by
      simp only [virtualVerticalPort] at ordered
      linarith
    exact_mod_cast realOrder
  have oldOrder := (perturbedColumnHeights_lt_iff planar straight columnBound firstMember secondMember right).mp shiftedOrder
  have firstHeight : (drawing.liftedStraightSegment first.1 first.2).rationalLineHeight column ∈ verticalCrossingHeights graph drawing column :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨first,firstMember,rfl⟩)
  have secondHeight : (drawing.liftedStraightSegment second.1 second.2).rationalLineHeight column ∈ verticalCrossingHeights graph drawing column :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨second,secondMember,rfl⟩)
  exact paddedCrossingHeights_strictMonoOn planar.1.1 degree column firstHeight secondHeight oldOrder

theorem virtualVerticalPort_before {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} (columnBound : column < drawing.gridSize) {first second : Nat × Cell}
    (firstMember : first ∈ verticalCrossingCopies graph drawing column)
    (secondMember : second ∈ verticalCrossingCopies graph drawing column) (right : Bool)
    (ordered : (virtualVerticalPort graph drawing column first right).Before (virtualVerticalPort graph drawing column second right)) :
    (finiteVerticalSlabPort graph drawing column first right).Before (finiteVerticalSlabPort graph drawing column second right) := by
  cases right
  · have coordinateOrder : (virtualVerticalPort graph drawing column first false).coordinate <
        (virtualVerticalPort graph drawing column second false).coordinate := by
      simpa [RealRectangleBoundary.Port.Before,RealRectangleBoundary.Port.clockwiseCode,
        Prod.Lex.toLex_lt_toLex,virtualVerticalPort] using ordered
    have mappedOrder := virtualVerticalPort_coordinate_order planar degree straight columnBound firstMember secondMember false coordinateOrder
    simpa [finiteVerticalSlabPort,OrthogonalBoundaryRouting.Port.Before] using mappedOrder
  · have coordinateOrder : (virtualVerticalPort graph drawing column second true).coordinate <
        (virtualVerticalPort graph drawing column first true).coordinate := by
      have realOrder : (perturbedColumnHeight graph drawing column second true : ℝ) <
          (perturbedColumnHeight graph drawing column first true : ℝ) := by
        simp [RealRectangleBoundary.Port.Before,RealRectangleBoundary.Port.clockwiseCode,
          Prod.Lex.toLex_lt_toLex,virtualVerticalPort] at ordered
        linarith
      dsimp only [virtualVerticalPort]
      linarith
    have mappedOrder := virtualVerticalPort_coordinate_order planar degree straight columnBound secondMember firstMember true coordinateOrder
    simpa [finiteVerticalSlabPort,OrthogonalBoundaryRouting.Port.Before] using mappedOrder

end LeanTrominoes.PeriodicGridDrawing
