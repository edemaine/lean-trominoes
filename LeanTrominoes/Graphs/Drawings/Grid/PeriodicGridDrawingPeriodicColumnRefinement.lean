/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingColumnCrossingBars
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPeriodicCrossingTable
import LeanTrominoes.Tiling.Periodic.PeriodicHeightRedistribution

/-! # Periodic crossing redistribution preserves row cells and crossing order -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

def periodicColumnHeight {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (height : ℚ) : Int :=
  periodicRedistributedHeight drawing.gridSize (OrthogonalDrawingRefinement.gridSize drawing.gridSize)
    (redistributedCrossingHeight graph drawing (line % (drawing.gridSize : Int))) height

theorem periodicColumnHeight_translate {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (height : ℚ) (shift : Cell) :
    periodicColumnHeight graph drawing (line+(drawing.gridSize : Int)*shift.1) (height+(drawing.gridSize : ℚ)*shift.2) =
      periodicColumnHeight graph drawing line height+(OrthogonalDrawingRefinement.gridSize drawing.gridSize : Int)*shift.2 := by
  have positive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  unfold periodicColumnHeight
  rw [Int.add_mul_emod_self_left]
  simpa only [Int.cast_natCast] using periodicRedistributedHeight_translate positive
    (OrthogonalDrawingRefinement.gridSize drawing.gridSize) _ height shift.2

theorem periodicColumnHeight_in_row {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) {line : Int}
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesVerticalLine line) :
    let height := (drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line
    (OrthogonalDrawingRefinement.gridSize drawing.gridSize : Int)*rationalCell drawing.gridSize height <
      periodicColumnHeight graph drawing line height ∧
    periodicColumnHeight graph drawing line height <
      (OrthogonalDrawingRefinement.gridSize drawing.gridSize : Int)*(rationalCell drawing.gridSize height+1) := by
  have heightMember := periodic_crossing_residue_mem compatible member straight edgeLocal cell crosses
  have bounds := redistributedCrossingHeight_in_cell compatible degree heightMember
  apply periodicRedistributedHeight_bounds
  exact ⟨by omega,by omega⟩

theorem periodicColumnHeight_preserves_order {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    {first second : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx) (secondMember : second ∈ graph.edges.zipIdx)
    (firstStraight : (drawing.edgeRoute first.2).length = 2) (secondStraight : (drawing.edgeRoute second.2).length = 2)
    (firstLocal : first.1.span ≤ 1) (secondLocal : second.1.span ≤ 1) (firstCell secondCell : Cell) {line : Int}
    (firstCrosses : (drawing.liftedStraightSegment first.2 firstCell).CrossesVerticalLine line)
    (secondCrosses : (drawing.liftedStraightSegment second.2 secondCell).CrossesVerticalLine line)
    (ordered : (drawing.liftedStraightSegment first.2 firstCell).rationalLineHeight line <
      (drawing.liftedStraightSegment second.2 secondCell).rationalLineHeight line) :
    periodicColumnHeight graph drawing line ((drawing.liftedStraightSegment first.2 firstCell).rationalLineHeight line) <
      periodicColumnHeight graph drawing line ((drawing.liftedStraightSegment second.2 secondCell).rationalLineHeight line) := by
  have gridPositive : 0 < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  have periodPositive : (0 : Int) < drawing.gridSize := by exact_mod_cast gridPositive
  have outputPositive : (0 : Int) < OrthogonalDrawingRefinement.gridSize drawing.gridSize := by
    exact_mod_cast OrthogonalDrawingRefinement.gridSize_positive gridPositive
  apply periodicRedistributedHeight_preserves_order periodPositive outputPositive _
    (verticalCrossingHeights graph drawing (line % (drawing.gridSize : Int)))
    (redistributedCrossingHeights_strictMonoOn compatible degree _)
    (fun _ member => ?_) (periodic_crossing_residue_mem compatible firstMember firstStraight firstLocal firstCell firstCrosses)
    (periodic_crossing_residue_mem compatible secondMember secondStraight secondLocal secondCell secondCrosses) ordered
  have bounds := redistributedCrossingHeight_in_cell compatible degree member
  exact ⟨by omega,by omega⟩

end LeanTrominoes.PeriodicGridDrawing
