/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingShiftedSeamGeometry
import LeanTrominoes.PeriodicGridDrawingPeriodicCrossingTable

/-! # The shifted row boundaries preserve every column crossing's row -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem seamPerturbation_below_row_gap {Vertex : Type*} {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    {column : Nat} (columnBound : column < drawing.gridSize) {key : Nat × Cell}
    (member : key ∈ verticalCrossingCopies graph drawing column) :
    seamPerturbation graph drawing < (drawing.gridSize : ℚ)-(drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column := by
  have upper := (of_decide_eq_true (List.mem_filter.mp member).2).2.2
  have constraints := seamRowConstraintValues_members columnBound member
  have zeroMember : ((0,0) : ℚ × ℚ) ∈ seamPerturbationValues graph drawing := List.mem_append.mpr (Or.inr constraints.1)
  have gapMember : ((drawing.gridSize : ℚ)-(drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column,1) ∈
      seamPerturbationValues graph drawing := List.mem_append.mpr (Or.inr constraints.2)
  have bound := seamPerturbation_le_pairBound zeroMember gapMember
  rw [pairBound_row_gap upper] at bound
  linarith

theorem shifted_row_bounds_for_column_crossing {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) {line : Int}
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesVerticalLine line) :
    let height := (drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line
    let row := rationalCell drawing.gridSize height
    (drawing.gridSize : ℚ)*row-seamPerturbation graph drawing < height ∧
      height < (drawing.gridSize : ℚ)*(row+1)-seamPerturbation graph drawing := by
  let height := (drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line
  have heightMember := periodic_crossing_residue_mem compatible member straight edgeLocal cell crosses
  obtain ⟨key,keyMember,heightEq⟩ := List.mem_map.mp (List.mem_toFinset.mp heightMember)
  have positive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  have lowerColumn := Int.emod_nonneg line positive.ne'
  have upperColumn := Int.emod_lt_of_pos line positive
  let column := (line % (drawing.gridSize : Int)).toNat
  have columnEq : (column : Int) = line % (drawing.gridSize : Int) := Int.toNat_of_nonneg lowerColumn
  have columnBound : column < drawing.gridSize := by omega
  have keyMemberNat : key ∈ verticalCrossingCopies graph drawing column := by simpa only [columnEq] using keyMember
  have gap := seamPerturbation_below_row_gap columnBound keyMemberNat
  rw [columnEq,heightEq] at gap
  have residueBounds := rationalResidue_bounds positive height
  have decomposition := rationalCoordinate_decomposition (drawing.gridSize : Int) height
  simp only [Int.cast_natCast] at decomposition
  have shiftPositive := seamPerturbation_positive graph drawing
  dsimp only
  constructor <;> nlinarith

end LeanTrominoes.PeriodicGridDrawing
