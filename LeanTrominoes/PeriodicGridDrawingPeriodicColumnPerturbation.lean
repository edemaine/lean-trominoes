/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingVirtualVerticalPortOrder

/-! # The column-cut perturbation is valid in every translated row and column -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement RationalPerturbation

theorem perturbedColumnHeight_translate {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (key : Nat × Cell) (shift : Cell) (right : Bool) :
    perturbedColumnHeight graph drawing (line+(drawing.gridSize : Int)*shift.1)
      (key.1,Cell.add key.2 shift) right = perturbedColumnHeight graph drawing line key right+(drawing.gridSize : ℚ)*shift.2 := by
  rw [perturbedColumnHeight_eq_evaluate,perturbedColumnHeight_eq_evaluate,liftedStraightSegment_add_cell]
  have lineEqual : line+(drawing.gridSize : Int)*shift.1 = line+(drawing.periodTranslation shift).1 := rfl
  rw [lineEqual,GridSegment.rationalLineHeight_translate,GridSegment.rationalSlope_translate]
  cases right <;> simp [evaluate,periodTranslation,Cell.scale] <;> ring

theorem perturbedColumnHeight_eq_row_evaluate {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (key : Nat × Cell) (right : Bool) :
    let height := (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight line
    perturbedColumnHeight graph drawing line key right =
      (drawing.gridSize : ℚ)*rationalCell drawing.gridSize height+evaluate (columnPerturbation graph drawing)
        (rationalResidue drawing.gridSize height,if right then -(drawing.liftedStraightSegment key.1 key.2).rationalSlope else
          (drawing.liftedStraightSegment key.1 key.2).rationalSlope) := by
  dsimp only
  rw [perturbedColumnHeight_eq_evaluate]
  simp only [evaluate,rationalResidue,Int.cast_natCast]
  ring

theorem periodic_columnPerturbation_values {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) {line : Int} (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesVerticalLine line) (right : Bool) :
    (rationalResidue drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line),
      if right then -(drawing.liftedStraightSegment tagged.2 cell).rationalSlope else
        (drawing.liftedStraightSegment tagged.2 cell).rationalSlope) ∈ columnPerturbationValues graph drawing := by
  let height := (drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line
  let reducedCell := Cell.add cell (Cell.scale (-1) (drawing.crossingReductionCell line height))
  have positive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  have lower := Int.emod_nonneg line positive.ne'
  have upper := Int.emod_lt_of_pos line positive
  let column := (line % (drawing.gridSize : Int)).toNat
  have columnEq : (column : Int) = line % (drawing.gridSize : Int) := Int.toNat_of_nonneg lower
  have columnBound : column < drawing.gridSize := by omega
  have reducedCrosses := crossingReduction_crosses crosses
  have reducedHeight := crossingReduction_height drawing tagged.2 cell line
  have reducedBounds : 0 ≤ (drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineHeight (line % (drawing.gridSize : Int)) ∧
      (drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineHeight (line % (drawing.gridSize : Int)) < (drawing.gridSize : ℚ) := by
    rw [show (drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineHeight (line % (drawing.gridSize : Int)) =
      rationalResidue drawing.gridSize height from reducedHeight]
    exact rationalResidue_bounds positive height
  have copied := verticalCrossingCopies_complete compatible member straight edgeLocal ⟨lower,upper.le⟩ reducedCell reducedCrosses reducedBounds
  have copiedNat : (tagged.2,reducedCell) ∈ verticalCrossingCopies graph drawing column := by
    simpa only [columnEq] using copied
  have values := mem_columnPerturbationValues_crossing columnBound copiedNat right
  rw [columnEq,reducedHeight] at values
  have sameSlope : (drawing.liftedStraightSegment tagged.2 reducedCell).rationalSlope =
      (drawing.liftedStraightSegment tagged.2 cell).rationalSlope := by
    rw [liftedStraightSegment_add_cell,GridSegment.rationalSlope_translate]
  simpa only [sameSlope] using values

theorem periodic_perturbedColumnHeight_row_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) {line : Int} (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesVerticalLine line) (right : Bool) :
    let height := (drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line
    let row := rationalCell drawing.gridSize height
    (drawing.gridSize : ℚ)*row-seamPerturbation graph drawing < perturbedColumnHeight graph drawing line (tagged.2,cell) right ∧
      perturbedColumnHeight graph drawing line (tagged.2,cell) right < (drawing.gridSize : ℚ)*(row+1)-seamPerturbation graph drawing := by
  let height := (drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line
  have originalBounds := shifted_row_bounds_for_column_crossing planar.1.1 member (straight tagged member) edgeLocal cell crosses
  have decomposition := rationalCoordinate_decomposition (drawing.gridSize : Int) height
  simp only [Int.cast_natCast] at decomposition
  have lowerOld : -seamPerturbation graph drawing < rationalResidue drawing.gridSize height := by
    dsimp only at originalBounds
    nlinarith [originalBounds.1]
  have upperOld : rationalResidue drawing.gridSize height < (drawing.gridSize : ℚ)-seamPerturbation graph drawing := by
    dsimp only at originalBounds
    nlinarith [originalBounds.2]
  have pointMember := periodic_columnPerturbation_values planar.1.1 member (straight tagged member) edgeLocal cell crosses right
  have rows := mem_columnPerturbationValues_rows graph drawing
  have lo := columnPerturbation_preserves_order planar straight rows.1 pointMember (Or.inl lowerOld)
  have hi := columnPerturbation_preserves_order planar straight pointMember rows.2 (Or.inl upperOld)
  simp only [evaluate,Prod.fst,Prod.snd,mul_zero,add_zero] at lo hi
  dsimp only
  rw [perturbedColumnHeight_eq_row_evaluate]
  dsimp only [evaluate]
  constructor <;> nlinarith

end LeanTrominoes.PeriodicGridDrawing
