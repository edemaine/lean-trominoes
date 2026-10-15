/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEndpointSeamAvoidance
import LeanTrominoes.Common.Geometry.GridSegmentShiftedSeamContactClassification
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleChordGeometry

/-! # Every nonvertical virtual row-seam contact has a retained table key -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem horizontal_cut_table_coverage {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) (row : Int) {coordinate : ℚ}
    (nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠ (drawing.liftedStraightSegment tagged.2 cell).finish.1)
    (inside : 0 < coordinate ∧ coordinate < (drawing.gridSize : ℚ))
    (contains : (drawing.liftedStraightSegment tagged.2 cell).RealContains
      ((coordinate : ℝ),((drawing.gridSize : ℚ)*row-seamPerturbation graph drawing : ℝ))) :
    ∃ key ∈ seamCrossingCopies graph drawing 0, key.1 = tagged.2 ∧
      Cell.add key.2 (0,row) = cell ∧ shiftedSeamAbscissa graph drawing key = coordinate := by
  have endpointAway := straight_lifted_endpoints_avoid_row_seam planar.1.1 member (straight tagged member) cell row
  have crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine ((drawing.gridSize : Int)*row) :=
    GridSegment.shifted_seam_contact_crosses (abscissa := (coordinate : ℝ))
      (seamPerturbation_positive graph drawing) (seamPerturbation_lt_one graph drawing)
      endpointAway.1 endpointAway.2
      (by simpa only [Int.cast_mul,Int.cast_natCast,Rat.cast_mul,Rat.cast_natCast,Rat.cast_intCast] using contains)
  have actual := row_shifted_seam_realInteriorContains (graph := graph) crosses
  have startAway : ((drawing.liftedStraightSegment tagged.2 cell).start.2 : ℝ) ≠
      ((drawing.gridSize : ℚ)*row-seamPerturbation graph drawing : ℝ) := by
    simpa only [if_true,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_intCast,Int.cast_mul,Int.cast_natCast,sub_eq_add_neg] using
      integer_ne_perturbed_cut ((drawing.gridSize : Int)*row) (drawing.liftedStraightSegment tagged.2 cell).start.2
        (seamPerturbation_positive graph drawing) (seamPerturbation_lt_one graph drawing) true
  have equalPoints := GridSegment.realContains_eq_of_same_y contains
    (GridSegment.realInteriorContains_implies_realContains actual) (by simp) startAway
  have coordinateEqual : coordinate = (drawing.liftedStraightSegment tagged.2 cell).rationalAbscissaAt
      ((drawing.gridSize : ℚ)*row-seamPerturbation graph drawing) := by
    have equalX := congrArg Prod.fst equalPoints
    dsimp only at equalX
    exact_mod_cast equalX
  have zeroX := straight_local_row_seam_cell_x_zero planar.1.1 member (straight tagged member) edgeLocal cell row crosses contains
    ⟨by dsimp only; exact_mod_cast inside.1,by dsimp only; exact_mod_cast inside.2⟩
  have oldBounds := (straight_local_row_seam_bounds planar.1.1 member (straight tagged member) edgeLocal cell row crosses).2
  simp only [zeroX,Int.cast_zero,mul_zero,zero_add,mul_one] at oldBounds
  let shift : Cell := (0,-row)
  let reducedCell := Cell.add cell shift
  have zeroLine : (0 : Int) = (drawing.gridSize : Int)*row+(drawing.periodTranslation shift).2 := by
    simp [shift,periodTranslation,Cell.scale]
  have reducedCrosses : (drawing.liftedStraightSegment tagged.2 reducedCell).CrossesHorizontalLine 0 := by
    rw [liftedStraightSegment_add_cell,zeroLine,GridSegment.crossesHorizontalLine_translate]
    exact crosses
  have oldCoordinateEqual : (drawing.liftedStraightSegment tagged.2 reducedCell).rationalLineAbscissa 0 =
      (drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa ((drawing.gridSize : Int)*row) := by
    rw [liftedStraightSegment_add_cell,zeroLine,GridSegment.rationalLineAbscissa_translate]
    simp [shift,periodTranslation,Cell.scale]
  have reducedNonvertical : (drawing.liftedStraightSegment tagged.2 reducedCell).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 reducedCell).finish.1 := by
    rw [liftedStraightSegment_add_cell]
    simpa [GridSegment.translate,Cell.add] using nonvertical
  have reducedMember := seamCrossingCopies_complete planar.1.1 member (straight tagged member) edgeLocal
    ⟨le_refl 0,Int.natCast_nonneg _⟩ reducedCell reducedCrosses
    (by simpa only [oldCoordinateEqual,Int.cast_mul,Int.cast_natCast] using And.intro oldBounds.1.le oldBounds.2) reducedNonvertical
  refine ⟨(tagged.2,reducedCell),reducedMember,rfl,?_,?_⟩
  · apply Prod.ext <;> simp [reducedCell,shift,Cell.add]
  · dsimp only [shiftedSeamAbscissa,Prod.fst,Prod.snd]
    rw [liftedStraightSegment_add_cell]
    have shiftedHeight : -seamPerturbation graph drawing =
        (drawing.gridSize : ℚ)*row-seamPerturbation graph drawing+(drawing.periodTranslation shift).2 := by
      simp [shift,periodTranslation,Cell.scale]
      ring
    rw [shiftedHeight,GridSegment.rationalAbscissaAt_translate]
    simpa [shift,periodTranslation,Cell.scale] using coordinateEqual.symm

end LeanTrominoes.PeriodicGridDrawing
