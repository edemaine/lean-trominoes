/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPeriodicColumnPerturbation

/-! # Proper vertical ports and their order in every periodic slab -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem perturbedColumnHeight_preserves_order_in_row {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first second : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx)
    (secondMember : second ∈ graph.edges.zipIdx) (firstLocal : first.1.span ≤ 1) (secondLocal : second.1.span ≤ 1)
    (firstCell secondCell : Cell) {line : Int}
    (firstCrosses : (drawing.liftedStraightSegment first.2 firstCell).CrossesVerticalLine line)
    (secondCrosses : (drawing.liftedStraightSegment second.2 secondCell).CrossesVerticalLine line)
    (sameRow : rationalCell drawing.gridSize ((drawing.liftedStraightSegment first.2 firstCell).rationalLineHeight line) =
      rationalCell drawing.gridSize ((drawing.liftedStraightSegment second.2 secondCell).rationalLineHeight line)) (right : Bool)
    (ordered : (drawing.liftedStraightSegment first.2 firstCell).rationalLineHeight line <
      (drawing.liftedStraightSegment second.2 secondCell).rationalLineHeight line) :
    perturbedColumnHeight graph drawing line (first.2,firstCell) right <
      perturbedColumnHeight graph drawing line (second.2,secondCell) right := by
  have firstAt := periodic_columnPerturbation_values planar.1.1 firstMember (straight first firstMember) firstLocal firstCell firstCrosses right
  have secondAt := periodic_columnPerturbation_values planar.1.1 secondMember (straight second secondMember) secondLocal secondCell secondCrosses right
  have residueOrder : rationalResidue drawing.gridSize ((drawing.liftedStraightSegment first.2 firstCell).rationalLineHeight line) <
      rationalResidue drawing.gridSize ((drawing.liftedStraightSegment second.2 secondCell).rationalLineHeight line) := by
    unfold rationalResidue
    rw [sameRow]
    linarith
  have moved := columnPerturbation_preserves_order planar straight firstAt secondAt (Or.inl residueOrder)
  rw [perturbedColumnHeight_eq_row_evaluate,perturbedColumnHeight_eq_row_evaluate,sameRow]
  dsimp only
  linarith

theorem perturbedColumnHeight_lt_iff_in_row {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first second : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx)
    (secondMember : second ∈ graph.edges.zipIdx) (firstLocal : first.1.span ≤ 1) (secondLocal : second.1.span ≤ 1)
    (firstCell secondCell : Cell) {line : Int}
    (firstCrosses : (drawing.liftedStraightSegment first.2 firstCell).CrossesVerticalLine line)
    (secondCrosses : (drawing.liftedStraightSegment second.2 secondCell).CrossesVerticalLine line)
    (sameRow : rationalCell drawing.gridSize ((drawing.liftedStraightSegment first.2 firstCell).rationalLineHeight line) =
      rationalCell drawing.gridSize ((drawing.liftedStraightSegment second.2 secondCell).rationalLineHeight line)) (right : Bool) :
    perturbedColumnHeight graph drawing line (first.2,firstCell) right < perturbedColumnHeight graph drawing line (second.2,secondCell) right ↔
      (drawing.liftedStraightSegment first.2 firstCell).rationalLineHeight line <
        (drawing.liftedStraightSegment second.2 secondCell).rationalLineHeight line := by
  constructor
  · intro ordered
    by_contra wrong
    rcases lt_or_eq_of_le (le_of_not_gt wrong) with reverse | equal
    · exact lt_asymm ordered (perturbedColumnHeight_preserves_order_in_row planar straight secondMember firstMember secondLocal firstLocal
        secondCell firstCell secondCrosses firstCrosses sameRow.symm right reverse)
    · by_cases same : (first.2,firstCell) = (second.2,secondCell)
      · rw [same] at ordered
        exact lt_irrefl _ ordered
      · have firstValid : first.2 < drawing.edgeRoutes.length := by
          rw [planar.1.1.2.2.1]
          exact List.snd_lt_of_mem_zipIdx firstMember
        have secondValid : second.2 < drawing.edgeRoutes.length := by
          rw [planar.1.1.2.2.1]
          exact List.snd_lt_of_mem_zipIdx secondMember
        exact vertical_crossing_heights_ne planar.2 firstValid secondValid (straight first firstMember) (straight second secondMember)
          firstCell secondCell same firstCrosses secondCrosses equal.symm
  · exact perturbedColumnHeight_preserves_order_in_row planar straight firstMember secondMember firstLocal secondLocal
      firstCell secondCell firstCrosses secondCrosses sameRow right

def periodicVirtualVerticalPort {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (key : Nat × Cell) (row : Int) (right : Bool) : RealRectangleBoundary.Port :=
  ⟨if right then 2 else 0,(perturbedColumnHeight graph drawing line key right : ℝ)+
    (seamPerturbation graph drawing : ℝ)-(drawing.gridSize : ℝ)*row⟩

theorem periodicVirtualVerticalPort_inside {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) {line : Int} (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesVerticalLine line) (right : Bool) :
    let row := rationalCell drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line)
    (periodicVirtualVerticalPort graph drawing line (tagged.2,cell) row right).Inside
      ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ) := by
  have bounds := periodic_perturbedColumnHeight_row_bounds planar straight member edgeLocal cell crosses right
  dsimp only at bounds ⊢
  have lo : (0 : ℚ) < perturbedColumnHeight graph drawing line (tagged.2,cell) right+seamPerturbation graph drawing-
      (drawing.gridSize : ℚ)*rationalCell drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line) := by linarith [bounds.1]
  have hi : perturbedColumnHeight graph drawing line (tagged.2,cell) right+seamPerturbation graph drawing-
      (drawing.gridSize : ℚ)*rationalCell drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line) < drawing.gridSize := by
    nlinarith [bounds.2]
  have realLo : (0 : ℝ) < (perturbedColumnHeight graph drawing line (tagged.2,cell) right : ℝ)+(seamPerturbation graph drawing : ℝ)-
      (drawing.gridSize : ℝ)*rationalCell drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line) := by exact_mod_cast lo
  have realHi : (perturbedColumnHeight graph drawing line (tagged.2,cell) right : ℝ)+(seamPerturbation graph drawing : ℝ)-
      (drawing.gridSize : ℝ)*rationalCell drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line) < drawing.gridSize := by exact_mod_cast hi
  cases right <;> simpa [periodicVirtualVerticalPort,RealRectangleBoundary.Port.Inside,RealRectangleBoundary.Port.extent] using And.intro realLo realHi

theorem periodicVirtualVerticalPort_point {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (key : Nat × Cell) (row : Int) (right : Bool) :
    (periodicVirtualVerticalPort graph drawing line key row right).shiftedPoint
      (virtualSlabOrigin graph drawing (columnPerturbation graph drawing) (line-if right then 1 else 0) row)
      ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ) =
    (((line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing) : ℝ),
      (perturbedColumnHeight graph drawing line key right : ℝ)) := by
  cases right <;> apply Prod.ext <;>
    simp [periodicVirtualVerticalPort,virtualSlabOrigin,RealRectangleBoundary.Port.shiftedPoint,RealRectangleBoundary.Port.point] <;> ring

theorem periodicVerticalPort_coordinate_order {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first second : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx)
    (secondMember : second ∈ graph.edges.zipIdx) (firstLocal : first.1.span ≤ 1) (secondLocal : second.1.span ≤ 1)
    (firstCell secondCell : Cell) {line : Int}
    (firstCrosses : (drawing.liftedStraightSegment first.2 firstCell).CrossesVerticalLine line)
    (secondCrosses : (drawing.liftedStraightSegment second.2 secondCell).CrossesVerticalLine line)
    (sameRow : rationalCell drawing.gridSize ((drawing.liftedStraightSegment first.2 firstCell).rationalLineHeight line) =
      rationalCell drawing.gridSize ((drawing.liftedStraightSegment second.2 secondCell).rationalLineHeight line)) (row : Int) (right : Bool)
    (ordered : (periodicVirtualVerticalPort graph drawing line (first.2,firstCell) row right).coordinate <
      (periodicVirtualVerticalPort graph drawing line (second.2,secondCell) row right).coordinate) :
    (paddedVerticalSlabPort graph drawing line ((drawing.liftedStraightSegment first.2 firstCell).rationalLineHeight line) row right).coordinate <
      (paddedVerticalSlabPort graph drawing line ((drawing.liftedStraightSegment second.2 secondCell).rationalLineHeight line) row right).coordinate := by
  have realOrder : (perturbedColumnHeight graph drawing line (first.2,firstCell) right : ℝ) <
      (perturbedColumnHeight graph drawing line (second.2,secondCell) right : ℝ) := by
    dsimp only [periodicVirtualVerticalPort] at ordered
    linarith
  have oldOrder := (perturbedColumnHeight_lt_iff_in_row planar straight firstMember secondMember firstLocal secondLocal firstCell secondCell
    firstCrosses secondCrosses sameRow right).mp (by exact_mod_cast realOrder)
  have newOrder := paddedPeriodicColumnHeight_preserves_order planar.1.1 degree firstMember secondMember (straight first firstMember)
    (straight second secondMember) firstLocal secondLocal firstCell secondCell firstCrosses secondCrosses oldOrder
  dsimp only [paddedVerticalSlabPort]
  omega

end LeanTrominoes.PeriodicGridDrawing
