/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingSeamCrossingCoordinates
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPeriodicHorizontalCrossingTable

/-! # Every nonvertical translated seam crossing has a finite-table port -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem seamCrossingCopies_complete {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1)
    {line : Int} (lineBounds : 0 ≤ line ∧ line ≤ drawing.gridSize) (cell : Cell)
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine line)
    (abscissaBounds : 0 ≤ (drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa line ∧
      (drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa line < (drawing.gridSize : ℚ))
    (nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 cell).finish.1) :
    (tagged.2,cell) ∈ seamCrossingCopies graph drawing line := by
  exact List.mem_filter.mpr ⟨horizontalCrossingCopies_complete compatible member straight edgeLocal
    lineBounds cell crosses abscissaBounds,by simpa using nonvertical⟩

theorem periodic_seam_crossing_reduced_key_mem {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) {line : Int}
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine line)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 cell).finish.1) :
    (tagged.2,Cell.add cell (Cell.scale (-1) (drawing.horizontalCrossingReductionCell line
      ((drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa line)))) ∈
        seamCrossingCopies graph drawing (line % (drawing.gridSize : Int)) := by
  let abscissa := (drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa line
  let reducedCell := Cell.add cell (Cell.scale (-1) (drawing.horizontalCrossingReductionCell line abscissa))
  have positive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  have lineBounds : 0 ≤ line % (drawing.gridSize : Int) ∧ line % (drawing.gridSize : Int) ≤ drawing.gridSize :=
    ⟨Int.emod_nonneg _ positive.ne',(Int.emod_lt_of_pos _ positive).le⟩
  have reducedAbscissa := horizontalCrossingReduction_abscissa drawing tagged.2 cell line
  have abscissaBounds : 0 ≤ (drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineAbscissa (line % (drawing.gridSize : Int)) ∧
      (drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineAbscissa (line % (drawing.gridSize : Int)) < (drawing.gridSize : ℚ) := by
    rw [show (drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineAbscissa (line % (drawing.gridSize : Int)) =
      rationalResidue drawing.gridSize abscissa from reducedAbscissa]
    exact rationalResidue_bounds positive abscissa
  have reducedNonvertical : (drawing.liftedStraightSegment tagged.2 reducedCell).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 reducedCell).finish.1 := by
    dsimp only [reducedCell]
    rw [liftedStraightSegment_add_cell]
    intro equal
    apply nonvertical
    simp only [GridSegment.translate,Cell.add,Prod.fst] at equal
    omega
  exact seamCrossingCopies_complete compatible member straight edgeLocal lineBounds reducedCell
    (horizontalCrossingReduction_crosses crosses) abscissaBounds reducedNonvertical

theorem periodic_seam_crossing_residue_mem {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) {line : Int}
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine line)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 cell).finish.1) :
    rationalResidue drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa line) ∈
      seamCrossingAbscissae graph drawing (line % (drawing.gridSize : Int)) := by
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,
    periodic_seam_crossing_reduced_key_mem compatible member straight edgeLocal cell crosses nonvertical,
    horizontalCrossingReduction_abscissa drawing tagged.2 cell line⟩)

end LeanTrominoes.PeriodicGridDrawing
