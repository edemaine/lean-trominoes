/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeDM.FiniteThreeDMNormalization
import LeanTrominoes.Graphs.Drawings.Grid.FiniteSparseDrawingSeam
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetSparseStripMotif

/-! # Finite normalized regions from sparse assignments -/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget FiniteSparseAssignmentSeamCompiler

variable {problem : PeriodicThreeDM} (presentation : problem.ContinuousPlanarPresentation)
variable (zero : problem.ZeroOffsets) (bounds : presentation.drawing.SegmentEndpointsInExpandedSquare)

def ContinuousPlanarPresentation.finiteSparseAssignments : List (Cell × OrthogonalCellType) :=
  (presentation.finitePad zero bounds).toPlanarPresentation.finalStripCellAssignments.map shift

def ContinuousPlanarPresentation.finiteSparseRegion (t : Tromino) : List Cell :=
  sparseExpandedMotif t (presentation.finiteSparseAssignments zero bounds)

theorem ContinuousPlanarPresentation.finitePaddedSparseFacts (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (simple : ∀ route∈presentation.drawing.edgeRoutes,LocalIncidenceDrawing.RouteIsSimple route) :
    let padded := presentation.finitePad zero bounds
    let planar := padded.toPlanarPresentation
    let drawing := planar.stripNormalizedOrthogonalDrawing
    (planar.finalStripCellAssignments.map Prod.fst).Nodup ∧
    (∀ assignment∈planar.finalStripCellAssignments,
      0<assignment.1.1 ∧ assignment.1.1<(drawing.horizontalPeriod:Int) ∧
      0<assignment.1.2 ∧ assignment.1.2<(drawing.verticalPeriod:Int)) ∧
    (∀ position : drawing.Position,drawing.get position=
      (planar.finalStripCellAssignments.lookup (((position.1.val:Int),(position.2.val:Int)):Cell)).getD .blank) ∧
    (∀ y,drawing.get (0,y)=.blank) ∧ (∀ x,drawing.get (x,0)=.blank) := by
  dsimp only
  let padded := presentation.finitePad zero bounds
  let planar := padded.toPlanarPresentation
  let drawing := planar.stripNormalizedOrthogonalDrawing
  have inside : padded.drawing.RoutePointsInFundamentalSquare :=
    presentation.finitePad_routePointsInFundamentalSquare zero bounds
  have band : padded.drawing.RoutePointsInExpandedVerticalBand := by
    intro route member point pointMember
    exact PeriodicGridDrawing.positionInExpandedVerticalBand_of_fundamentalSquare
      (inside route member point pointMember)
  have paddedSeparated : padded.drawing.LiftedRoutesAvoidEachOther :=
    PeriodicGridDrawing.finitePad_liftedRoutesAvoidEachOther inside separated
  have paddedSimple : ∀ route∈padded.drawing.edgeRoutes,LocalIncidenceDrawing.RouteIsSimple route :=
    PeriodicGridDrawing.finitePad_routesSimple simple
  refine ⟨padded.finalStripAssignmentsCollisionFree wellFormed degree paddedSeparated paddedSimple,?_,?_,
    padded.stripNormalizedOrthogonalDrawing_first_column_blank wellFormed degree zero inside,?_⟩
  · intro assignment member
    have xPositive := padded.finalStripCellAssignment_horizontal_pos wellFormed degree zero inside member
    have xBound := planar.finalStripCellAssignment_horizontal_bounds member
    have yBound := padded.finalStripCellAssignment_vertical_interior wellFormed degree zero.isOneDimensional band member
    have periodEq : drawing.horizontalPeriod=planar.finalNormalizationPeriod :=
      planar.stripNormalizedOrthogonalDrawing_periods.1
    have heightEq : drawing.verticalPeriod=planar.finalStripHeight :=
      planar.stripNormalizedOrthogonalDrawing_periods.2
    rw [periodEq,heightEq]
    unfold PlanarPresentation.finalStripHeight
    have yBound' : assignment.1.2 < 3*(planar.finalNormalizationPeriod:Int) := yBound.2
    exact ⟨xPositive,xBound.2,yBound.1,by omega⟩
  · intro position
    exact planar.stripNormalizedOrthogonalDrawing_get position
  · intro x
    exact ((PeriodicOrthogonalDrawing.blankVerticalBoundary_iff_rows drawing).mp
      (padded.stripNormalizedOrthogonalDrawing_hasBlankVerticalBoundary
        wellFormed degree zero.isOneDimensional band) x).1

/-- Sparse assignment order can differ from dense raster order, but the
finite target carrier is identical. -/
theorem ContinuousPlanarPresentation.finiteSparseRegion_carrier_eq
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (simple : ∀ route∈presentation.drawing.edgeRoutes,LocalIncidenceDrawing.RouteIsSimple route) (t : Tromino) :
    ((presentation.finiteSparseRegion zero bounds t).toFinset:Set Cell)=
      ((presentation.finiteNormalizedDrawing zero bounds).expandedMotif t).toFinset := by
  obtain ⟨nodup,assignmentBounds,readback,firstColumn,firstRow⟩ :=
    presentation.finitePaddedSparseFacts zero bounds wellFormed degree separated simple
  apply Set.ext
  intro cell
  simp only [Finset.mem_coe,List.mem_toFinset]
  exact mem_shiftedMotif_iff _ _ nodup assignmentBounds readback firstColumn firstRow t cell

/-- The source perfect matching problem reduces to the finite sparse region. -/
theorem ContinuousPlanarPresentation.finiteSparseRegion_correct
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (simple : ∀ route∈presentation.drawing.edgeRoutes,LocalIncidenceDrawing.RouteIsSimple route) (t : Tromino) :
    problem.FiniteSatisfiable ↔ t.Tileable ((presentation.finiteSparseRegion zero bounds t).toFinset:Set Cell) := by
  rw [presentation.finiteSparseRegion_carrier_eq zero bounds wellFormed degree separated simple]
  exact presentation.finiteTrominoRegion_correct wellFormed degree zero bounds separated simple t
end LeanTrominoes.PeriodicThreeDM
