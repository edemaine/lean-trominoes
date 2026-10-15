/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPeriodicSeamCoordinates

/-! # Slope-biased integral ports for actual translated row-seam crossings -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem row_seam_crossing_residue_mem {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) (row : Int)
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine ((drawing.gridSize : Int)*row))
    (nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠ (drawing.liftedStraightSegment tagged.2 cell).finish.1) :
    rationalResidue drawing.gridSize ((drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa ((drawing.gridSize : Int)*row)) ∈
      seamCrossingAbscissae graph drawing 0 := by
  simpa using periodic_seam_crossing_residue_mem compatible member straight edgeLocal cell crosses nonvertical

theorem row_seam_crossing_bias {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) (row : Int)
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine ((drawing.gridSize : Int)*row))
    (nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠ (drawing.liftedStraightSegment tagged.2 cell).finish.1) :
    seamTowardLeft graph drawing 0 (rationalResidue drawing.gridSize
      ((drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa ((drawing.gridSize : Int)*row))) =
        decide (0 < (drawing.liftedStraightSegment tagged.2 cell).rationalSlope) := by
  have reducedMember := periodic_seam_crossing_reduced_key_mem planar.1.1 member (straight tagged member)
    edgeLocal cell crosses nonvertical
  have bias := seamTowardLeft_at_key planar straight _ reducedMember
  rw [horizontalCrossingReduction_abscissa] at bias
  rw [liftedStraightSegment_add_cell,GridSegment.rationalSlope_translate] at bias
  simpa using bias

theorem row_seam_integral_column_bias {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) (row column : Int)
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine ((drawing.gridSize : Int)*row))
    (nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠ (drawing.liftedStraightSegment tagged.2 cell).finish.1)
    (integral : (drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa ((drawing.gridSize : Int)*row) = (column : ℚ)) :
    periodicSeamSlab graph drawing ((drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa ((drawing.gridSize : Int)*row)) =
      if 0 < (drawing.liftedStraightSegment tagged.2 cell).rationalSlope then column-1 else column := by
  unfold periodicSeamSlab
  rw [row_seam_crossing_bias planar straight member edgeLocal cell row crosses nonvertical,integral]
  simp [rationalSlab]

theorem row_seam_port_slab_clearance {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) (row : Int)
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine ((drawing.gridSize : Int)*row))
    (nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠ (drawing.liftedStraightSegment tagged.2 cell).finish.1) :
    let abscissa := (drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa ((drawing.gridSize : Int)*row)
    (paddedRefinementFactor drawing.gridSize : Int)*periodicSeamSlab graph drawing abscissa+7*crossingBound drawing.gridSize <
      periodicSeamCoordinate graph drawing abscissa ∧
    periodicSeamCoordinate graph drawing abscissa <
      (paddedRefinementFactor drawing.gridSize : Int)*(periodicSeamSlab graph drawing abscissa+1)-7*crossingBound drawing.gridSize :=
  periodicSeamCoordinate_slab_clearance compatible degree
    (row_seam_crossing_residue_mem compatible member straight edgeLocal cell row crosses nonvertical)

end LeanTrominoes.PeriodicGridDrawing
