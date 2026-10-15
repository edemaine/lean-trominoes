/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingShiftedSeamPorts
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingSeamPortGeometry
import LeanTrominoes.Common.Geometry.GridSegmentRationalSeamPerturbationTranslation

/-! # One rational row-seam shift works for every translated edge occurrence -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem seamPerturbation_lt_one {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) :
    seamPerturbation graph drawing < 1 := RationalPerturbation.slabPerturbation_lt_one _

theorem row_seam_perturbation_small {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) (row : Int)
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine ((drawing.gridSize : Int)*row))
    (nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠ (drawing.liftedStraightSegment tagged.2 cell).finish.1) :
    seamPerturbation graph drawing < rationalSlabMargin
      ((drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa ((drawing.gridSize : Int)*row))
      (drawing.liftedStraightSegment tagged.2 cell).horizontalSeamVelocity := by
  let line := (drawing.gridSize : Int)*row
  let abscissa := (drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa line
  let reducedCell := Cell.add cell (Cell.scale (-1) (drawing.horizontalCrossingReductionCell line abscissa))
  have reducedMember : (tagged.2,reducedCell) ∈ seamCrossingCopies graph drawing 0 := by
    simpa using periodic_seam_crossing_reduced_key_mem compatible member straight edgeLocal cell crosses nonvertical
  have reducedAbscissa : (drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineAbscissa 0 =
      rationalResidue drawing.gridSize abscissa := by
    simpa [line,abscissa,reducedCell] using horizontalCrossingReduction_abscissa drawing tagged.2 cell line
  have reducedVelocity : (drawing.liftedStraightSegment tagged.2 reducedCell).horizontalSeamVelocity =
      (drawing.liftedStraightSegment tagged.2 cell).horizontalSeamVelocity := by
    dsimp only [reducedCell]
    rw [liftedStraightSegment_add_cell,GridSegment.horizontalSeamVelocity_translate]
  have bound := RationalPerturbation.slabPerturbation_lt_slabMargin (mem_seamPerturbationValues reducedMember)
  change seamPerturbation graph drawing < rationalSlabMargin
    ((drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineAbscissa 0)
    (drawing.liftedStraightSegment tagged.2 reducedCell).horizontalSeamVelocity at bound
  rw [reducedAbscissa,reducedVelocity] at bound
  rw [rationalSlabMargin_residue drawing.gridSize _ _]
  exact bound

theorem row_shifted_seam_slab {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) (row : Int)
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine ((drawing.gridSize : Int)*row))
    (nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠ (drawing.liftedStraightSegment tagged.2 cell).finish.1) :
    rationalSlab ((drawing.liftedStraightSegment tagged.2 cell).rationalAbscissaAt
      (((drawing.gridSize : Int)*row : ℚ)-seamPerturbation graph drawing)) false =
    periodicSeamSlab graph drawing ((drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa ((drawing.gridSize : Int)*row)) := by
  unfold periodicSeamSlab
  rw [row_seam_crossing_bias planar straight member edgeLocal cell row crosses nonvertical]
  simpa only [Int.cast_mul] using GridSegment.shifted_horizontal_seam_slab (seamPerturbation_positive graph drawing)
    (row_seam_perturbation_small planar.1.1 member (straight tagged member) edgeLocal cell row crosses nonvertical)

theorem row_shifted_seam_realInteriorContains {Vertex : Type*} {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} {index : Nat} {cell : Cell} {row : Int}
    (crosses : (drawing.liftedStraightSegment index cell).CrossesHorizontalLine ((drawing.gridSize : Int)*row)) :
    (drawing.liftedStraightSegment index cell).RealInteriorContains
      (((drawing.liftedStraightSegment index cell).rationalAbscissaAt
        (((drawing.gridSize : Int)*row : ℚ)-seamPerturbation graph drawing) : ℝ),
        (((drawing.gridSize : Int)*row : ℚ)-seamPerturbation graph drawing : ℝ)) := by
  simpa only [Int.cast_mul,Rat.cast_mul,Rat.cast_intCast] using GridSegment.shifted_horizontal_seam_realInteriorContains crosses
    (seamPerturbation_positive graph drawing) (seamPerturbation_lt_one graph drawing)

end LeanTrominoes.PeriodicGridDrawing
