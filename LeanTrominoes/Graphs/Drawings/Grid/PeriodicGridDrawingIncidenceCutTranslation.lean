/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVirtualIncidencePorts

/-! # Translated incidence cuts remain in their vertex's row and column cell -/
namespace LeanTrominoes.PeriodicGridDrawing
open GeneralVertexNormalization

theorem translated_outward_cut_height {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) (target left : Bool) (cell : Cell) :
    ((drawing.outwardStraightSegment tagged target).translate (drawing.periodTranslation cell)).rationalHeightAt
      (((drawing.outwardStraightSegment tagged target).start.1 : ℚ)+
        (if left then -columnPerturbation graph drawing else columnPerturbation graph drawing)+(drawing.periodTranslation cell).1) =
      perturbedIncidenceHeight graph drawing tagged target left+(drawing.gridSize : ℚ)*cell.2 := by
  rw [GridSegment.rationalHeightAt_translate]
  simp only [perturbedIncidenceHeight,periodTranslation,Cell.scale,Int.cast_mul,Int.cast_natCast]

theorem translated_incidence_cut_row_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (target left : Bool) (cell : Cell) :
    (drawing.gridSize : ℚ)*cell.2-seamPerturbation graph drawing <
        perturbedIncidenceHeight graph drawing tagged target left+(drawing.gridSize : ℚ)*cell.2 ∧
      perturbedIncidenceHeight graph drawing tagged target left+(drawing.gridSize : ℚ)*cell.2 <
        (drawing.gridSize : ℚ)*(cell.2+1)-seamPerturbation graph drawing := by
  have bounds := perturbedIncidenceHeight_in_row planar straight member target left
  constructor <;> nlinarith [bounds.1,bounds.2]

theorem translated_incidence_cut_row_zero {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (target left : Bool) (cell : Cell)
    (inside : -seamPerturbation graph drawing < perturbedIncidenceHeight graph drawing tagged target left+(drawing.gridSize : ℚ)*cell.2 ∧
      perturbedIncidenceHeight graph drawing tagged target left+(drawing.gridSize : ℚ)*cell.2 <
        (drawing.gridSize : ℚ)-seamPerturbation graph drawing) : cell.2 = 0 := by
  have bounds := translated_incidence_cut_row_bounds planar straight member target left cell
  have gridPositive : (0 : ℚ) < drawing.gridSize := by
    have positive : 0 < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
    exact_mod_cast positive
  have lowerScaled : (drawing.gridSize : ℚ)*(-1) < (drawing.gridSize : ℚ)*cell.2 := by nlinarith [bounds.2,inside.1]
  have upperScaled : (drawing.gridSize : ℚ)*cell.2 < (drawing.gridSize : ℚ)*1 := by nlinarith [bounds.1,inside.2]
  have lower : (-1 : ℚ) < cell.2 := by nlinarith
  have upper : (cell.2 : ℚ) < 1 := by nlinarith
  have lowerInt : -1 < cell.2 := by exact_mod_cast lower
  have upperInt : cell.2 < 1 := by exact_mod_cast upper
  omega

theorem translated_incidence_column_zero {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (target : Bool) (cell : Cell) {line : Int}
    (lineBounds : 0 ≤ line ∧ line ≤ drawing.gridSize)
    (sameX : (drawing.outwardStraightSegment tagged target).start.1+(drawing.gridSize : Int)*cell.1 = line) : cell.1 = 0 := by
  have bounds := outwardStraightSegment_start_bounds compatible member target
  have gridPositive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  by_contra wrong
  rcases lt_or_gt_of_ne wrong with negative | positive
  · have cellBound : cell.1 ≤ -1 := by omega
    have scaled := mul_le_mul_of_nonneg_left cellBound gridPositive.le
    nlinarith [bounds.2.1,lineBounds.1]
  · have cellBound : 1 ≤ cell.1 := by omega
    have scaled := mul_le_mul_of_nonneg_left cellBound gridPositive.le
    nlinarith [bounds.1,lineBounds.2]

theorem translated_incidence_cell_zero {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (target left : Bool) (cell : Cell) {line : Int}
    (lineBounds : 0 ≤ line ∧ line ≤ drawing.gridSize)
    (sameX : (drawing.outwardStraightSegment tagged target).start.1+(drawing.gridSize : Int)*cell.1 = line)
    (inside : -seamPerturbation graph drawing < perturbedIncidenceHeight graph drawing tagged target left+(drawing.gridSize : ℚ)*cell.2 ∧
      perturbedIncidenceHeight graph drawing tagged target left+(drawing.gridSize : ℚ)*cell.2 <
        (drawing.gridSize : ℚ)-seamPerturbation graph drawing) : cell = (0,0) :=
  Prod.ext (translated_incidence_column_zero planar.1.1 member target cell lineBounds sameX)
    (translated_incidence_cut_row_zero planar straight member target left cell inside)

end LeanTrominoes.PeriodicGridDrawing
