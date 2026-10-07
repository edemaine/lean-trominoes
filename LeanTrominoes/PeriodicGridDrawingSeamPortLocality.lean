/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingSeamPortGeometry

/-! # Redistributed row-seam ports stay in their original column cell -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem row_seam_port_column_locality {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal) (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) (row : Int)
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine ((drawing.gridSize : Int)*row))
    (nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠ (drawing.liftedStraightSegment tagged.2 cell).finish.1) :
    let abscissa := (drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa ((drawing.gridSize : Int)*row)
    (paddedGridSize drawing.gridSize : Int)*cell.1 < periodicSeamCoordinate graph drawing abscissa ∧
      periodicSeamCoordinate graph drawing abscissa < (paddedGridSize drawing.gridSize : Int)*(cell.1+1) := by
  let abscissa := (drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa ((drawing.gridSize : Int)*row)
  have edgeLocal := graphLocal _ (List.fst_mem_of_mem_zipIdx member)
  have oldBounds := (straight_local_row_seam_bounds compatible member (straight tagged member) edgeLocal cell row crosses).2
  have positive : (0 : ℚ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have quotient : rationalCell drawing.gridSize abscissa = cell.1 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (le_div_iff₀ positive).mpr
      dsimp only [abscissa]
      nlinarith [oldBounds.1]
    · apply (div_lt_iff₀ positive).mpr
      nlinarith [oldBounds.2]
  have residueMember := row_seam_crossing_residue_mem compatible member (straight tagged member) edgeLocal cell row crosses nonvertical
  have bounds := periodicRedistributedHeight_bounds (seamCrossingCoordinate graph drawing 0) abscissa
    (seamCrossingCoordinate_in_cell compatible degree graphLocal straight residueMember)
  simpa only [periodicSeamCoordinate,quotient] using bounds

theorem row_seam_ports_preserve_order {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal) (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first second : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx) (secondMember : second ∈ graph.edges.zipIdx)
    (firstCell secondCell : Cell) (row : Int)
    (firstCrosses : (drawing.liftedStraightSegment first.2 firstCell).CrossesHorizontalLine ((drawing.gridSize : Int)*row))
    (secondCrosses : (drawing.liftedStraightSegment second.2 secondCell).CrossesHorizontalLine ((drawing.gridSize : Int)*row))
    (firstNonvertical : (drawing.liftedStraightSegment first.2 firstCell).start.1 ≠ (drawing.liftedStraightSegment first.2 firstCell).finish.1)
    (secondNonvertical : (drawing.liftedStraightSegment second.2 secondCell).start.1 ≠ (drawing.liftedStraightSegment second.2 secondCell).finish.1)
    (ordered : (drawing.liftedStraightSegment first.2 firstCell).rationalLineAbscissa ((drawing.gridSize : Int)*row) <
      (drawing.liftedStraightSegment second.2 secondCell).rationalLineAbscissa ((drawing.gridSize : Int)*row)) :
    periodicSeamCoordinate graph drawing ((drawing.liftedStraightSegment first.2 firstCell).rationalLineAbscissa ((drawing.gridSize : Int)*row)) <
      periodicSeamCoordinate graph drawing ((drawing.liftedStraightSegment second.2 secondCell).rationalLineAbscissa ((drawing.gridSize : Int)*row)) :=
  periodicSeamCoordinate_preserves_order compatible degree graphLocal straight
    (row_seam_crossing_residue_mem compatible firstMember (straight first firstMember)
      (graphLocal _ (List.fst_mem_of_mem_zipIdx firstMember)) firstCell row firstCrosses firstNonvertical)
    (row_seam_crossing_residue_mem compatible secondMember (straight second secondMember)
      (graphLocal _ (List.fst_mem_of_mem_zipIdx secondMember)) secondCell row secondCrosses secondNonvertical) ordered

end LeanTrominoes.PeriodicGridDrawing
