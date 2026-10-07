/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingPeriodicCrossingTable
import LeanTrominoes.PeriodicGridDrawingHorizontalCrossingEnumeration

/-! # Every translated row-seam crossing reduces to the finite horizontal table -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

def horizontalCrossingReductionCell (drawing : PeriodicGridDrawing) (line : Int) (abscissa : ℚ) : Cell :=
  (rationalCell drawing.gridSize abscissa,line/(drawing.gridSize : Int))

theorem horizontalCrossingReduction_line (drawing : PeriodicGridDrawing) (line : Int) (abscissa : ℚ) :
    line % (drawing.gridSize : Int) = line+
      (drawing.periodTranslation (Cell.scale (-1) (drawing.horizontalCrossingReductionCell line abscissa))).2 := by
  have decomposition := Int.emod_add_ediv_mul line (drawing.gridSize : Int)
  simp only [periodTranslation,Cell.scale,horizontalCrossingReductionCell]
  nlinarith

theorem horizontalCrossingReduction_crosses {drawing : PeriodicGridDrawing} {index : Nat} {cell : Cell} {line : Int}
    (crosses : (drawing.liftedStraightSegment index cell).CrossesHorizontalLine line) :
    (drawing.liftedStraightSegment index (Cell.add cell (Cell.scale (-1)
      (drawing.horizontalCrossingReductionCell line ((drawing.liftedStraightSegment index cell).rationalLineAbscissa line))))).CrossesHorizontalLine
        (line % (drawing.gridSize : Int)) := by
  rw [liftedStraightSegment_add_cell,horizontalCrossingReduction_line,GridSegment.crossesHorizontalLine_translate]
  exact crosses

theorem horizontalCrossingReduction_abscissa (drawing : PeriodicGridDrawing) (index : Nat) (cell : Cell) (line : Int) :
    (drawing.liftedStraightSegment index (Cell.add cell (Cell.scale (-1)
      (drawing.horizontalCrossingReductionCell line ((drawing.liftedStraightSegment index cell).rationalLineAbscissa line))))).rationalLineAbscissa
        (line % (drawing.gridSize : Int)) =
      rationalResidue drawing.gridSize ((drawing.liftedStraightSegment index cell).rationalLineAbscissa line) := by
  rw [liftedStraightSegment_add_cell,horizontalCrossingReduction_line,GridSegment.rationalLineAbscissa_translate]
  simp only [periodTranslation,Cell.scale,horizontalCrossingReductionCell,rationalResidue,Int.cast_mul,Int.cast_neg,Int.cast_one]
  ring

theorem periodic_horizontal_crossing_residue_mem {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) {line : Int}
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine line) :
    rationalResidue drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa line) ∈
      horizontalCrossingAbscissae graph drawing (line % (drawing.gridSize : Int)) := by
  let abscissa := (drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa line
  let reducedCell := Cell.add cell (Cell.scale (-1) (drawing.horizontalCrossingReductionCell line abscissa))
  have positive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  have lineBounds : 0 ≤ line % (drawing.gridSize : Int) ∧ line % (drawing.gridSize : Int) ≤ drawing.gridSize :=
    ⟨Int.emod_nonneg _ positive.ne',(Int.emod_lt_of_pos _ positive).le⟩
  have reducedCrosses := horizontalCrossingReduction_crosses crosses
  have reducedAbscissa := horizontalCrossingReduction_abscissa drawing tagged.2 cell line
  have abscissaBounds : 0 ≤ (drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineAbscissa (line % (drawing.gridSize : Int)) ∧
      (drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineAbscissa (line % (drawing.gridSize : Int)) < (drawing.gridSize : ℚ) := by
    rw [show (drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineAbscissa (line % (drawing.gridSize : Int)) =
      rationalResidue drawing.gridSize abscissa from reducedAbscissa]
    exact rationalResidue_bounds positive abscissa
  have copied := horizontalCrossingCopies_complete compatible member straight edgeLocal lineBounds reducedCell reducedCrosses abscissaBounds
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(tagged.2,reducedCell),copied,reducedAbscissa⟩)

end LeanTrominoes.PeriodicGridDrawing
