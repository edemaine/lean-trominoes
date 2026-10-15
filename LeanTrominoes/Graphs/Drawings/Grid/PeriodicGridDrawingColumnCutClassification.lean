/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPeriodicColumnPortTransport

/-! # Proper column crossings in the virtual fundamental row are retained -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem perturbed_column_crossing_row_zero {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) {line : Int} (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesVerticalLine line) (right : Bool)
    (inside : -seamPerturbation graph drawing < perturbedColumnHeight graph drawing line (tagged.2,cell) right ∧
      perturbedColumnHeight graph drawing line (tagged.2,cell) right < (drawing.gridSize : ℚ)-seamPerturbation graph drawing) :
    rationalCell drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line) = 0 := by
  have bounds := periodic_perturbedColumnHeight_row_bounds planar straight member edgeLocal cell crosses right
  dsimp only at bounds
  have gridPositive : (0 : ℚ) < drawing.gridSize := by
    have positive : 0 < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
    exact_mod_cast positive
  have lower : (-1 : ℚ) < rationalCell drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line) := by
    nlinarith [bounds.2,inside.1]
  have upper : (rationalCell drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line) : ℚ) < 1 := by
    nlinarith [bounds.1,inside.2]
  have lowerInt : -1 < rationalCell drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line) := by exact_mod_cast lower
  have upperInt : rationalCell drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line) < 1 := by exact_mod_cast upper
  omega

theorem column_crossing_retained_of_virtual_row {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) {line : Int} (lineBounds : 0 ≤ line ∧ line ≤ drawing.gridSize)
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesVerticalLine line) (right : Bool)
    (inside : -seamPerturbation graph drawing < perturbedColumnHeight graph drawing line (tagged.2,cell) right ∧
      perturbedColumnHeight graph drawing line (tagged.2,cell) right < (drawing.gridSize : ℚ)-seamPerturbation graph drawing) :
    (ColumnPortKey.crossing (tagged.2,cell)).Valid graph drawing line right := by
  have rowZero := perturbed_column_crossing_row_zero planar straight member edgeLocal cell crosses right inside
  have positive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  have bounds := rationalResidue_bounds positive ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line)
  simp only [rationalResidue,rowZero,Int.cast_zero,mul_zero,sub_zero] at bounds
  exact verticalCrossingCopies_complete planar.1.1 member (straight tagged member) edgeLocal lineBounds cell crosses bounds

end LeanTrominoes.PeriodicGridDrawing
