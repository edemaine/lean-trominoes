/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingVerticalCrossingEnumeration
import LeanTrominoes.GridSegmentRationalCrossingTranslation
import LeanTrominoes.RationalPeriodicCoordinates

/-! # The finite crossing table represents crossings in every translated cell -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem liftedStraightSegment_add_cell (drawing : PeriodicGridDrawing) (index : Nat) (cell shift : Cell) :
    drawing.liftedStraightSegment index (Cell.add cell shift) =
      (drawing.liftedStraightSegment index cell).translate (drawing.periodTranslation shift) := by
  apply congrArg₂ GridSegment.mk <;> apply Prod.ext <;>
    simp [liftedStraightSegment,GridSegment.translate,periodTranslation,Cell.add,Cell.scale] <;> ring

def crossingReductionCell (drawing : PeriodicGridDrawing) (line : Int) (height : ℚ) : Cell :=
  (line/(drawing.gridSize : Int),rationalCell drawing.gridSize height)

theorem crossingReduction_line (drawing : PeriodicGridDrawing) (line : Int) (height : ℚ) :
    line % (drawing.gridSize : Int) = line+
      (drawing.periodTranslation (Cell.scale (-1) (drawing.crossingReductionCell line height))).1 := by
  have decomposition := Int.emod_add_ediv_mul line (drawing.gridSize : Int)
  simp only [periodTranslation,Cell.scale,crossingReductionCell]
  nlinarith

theorem crossingReduction_crosses {drawing : PeriodicGridDrawing} {index : Nat} {cell : Cell} {line : Int}
    (crosses : (drawing.liftedStraightSegment index cell).CrossesVerticalLine line) :
    (drawing.liftedStraightSegment index (Cell.add cell (Cell.scale (-1)
      (drawing.crossingReductionCell line ((drawing.liftedStraightSegment index cell).rationalLineHeight line))))).CrossesVerticalLine
        (line % (drawing.gridSize : Int)) := by
  rw [liftedStraightSegment_add_cell,crossingReduction_line,GridSegment.crossesVerticalLine_translate]
  exact crosses

theorem crossingReduction_height (drawing : PeriodicGridDrawing) (index : Nat) (cell : Cell) (line : Int) :
    (drawing.liftedStraightSegment index (Cell.add cell (Cell.scale (-1)
      (drawing.crossingReductionCell line ((drawing.liftedStraightSegment index cell).rationalLineHeight line))))).rationalLineHeight
        (line % (drawing.gridSize : Int)) =
      rationalResidue drawing.gridSize ((drawing.liftedStraightSegment index cell).rationalLineHeight line) := by
  rw [liftedStraightSegment_add_cell,crossingReduction_line,GridSegment.rationalLineHeight_translate]
  simp only [periodTranslation,Cell.scale,crossingReductionCell,rationalResidue,Int.cast_mul,Int.cast_neg,Int.cast_one]
  ring

theorem periodic_crossing_residue_mem {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) {line : Int}
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesVerticalLine line) :
    rationalResidue drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line) ∈
      verticalCrossingHeights graph drawing (line % (drawing.gridSize : Int)) := by
  let height := (drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line
  let reducedCell := Cell.add cell (Cell.scale (-1) (drawing.crossingReductionCell line height))
  have positive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  have lineBounds : 0 ≤ line % (drawing.gridSize : Int) ∧ line % (drawing.gridSize : Int) ≤ drawing.gridSize :=
    ⟨Int.emod_nonneg _ positive.ne', (Int.emod_lt_of_pos _ positive).le⟩
  have reducedCrosses := crossingReduction_crosses crosses
  have reducedHeight := crossingReduction_height drawing tagged.2 cell line
  have heightBounds : 0 ≤ (drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineHeight (line % (drawing.gridSize : Int)) ∧
      (drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineHeight (line % (drawing.gridSize : Int)) < (drawing.gridSize : ℚ) := by
    rw [show (drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineHeight (line % (drawing.gridSize : Int)) =
      rationalResidue drawing.gridSize height from reducedHeight]
    exact rationalResidue_bounds positive height
  have copied := verticalCrossingCopies_complete compatible member straight edgeLocal lineBounds reducedCell reducedCrosses heightBounds
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  exact ⟨(tagged.2,reducedCell),copied,reducedHeight⟩

end LeanTrominoes.PeriodicGridDrawing
