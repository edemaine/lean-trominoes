/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeDM.FiniteThreeDMPaddedPresentation
import LeanTrominoes.Graphs.Drawings.Grid.FiniteGridDrawingPaddingSeparation
import LeanTrominoes.Tiling.Tromino.Finite.FiniteNormalizationBlankColumn
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalDrawingMoveSeam
import LeanTrominoes.Graphs.Orientation.NormalizedOrientationFiniteCoordinates
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMNormalizationStripBlankBoundary
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMNormalizationStripOrientationEquivalence
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMNormalizationStripWellFormed
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMNormalizationStripVertexSeparation
import LeanTrominoes.ThreeDM.FiniteThreeDMSemantics

/-! # Finite zero-offset 3DM instances normalize to bounded tromino regions -/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget

theorem ZeroOffsets.isOneDimensional {problem : PeriodicThreeDM} (zero : problem.ZeroOffsets) :
    problem.IsOneDimensional := by
  intro triple member color
  exact congrArg Prod.snd (zero triple member color)

def ContinuousPlanarPresentation.finiteNormalizedDrawing {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation) (zero : problem.ZeroOffsets)
    (bounds : presentation.drawing.SegmentEndpointsInExpandedSquare) : PeriodicOrthogonalDrawing :=
  (presentation.finitePad zero bounds).toPlanarPresentation.stripNormalizedOrthogonalDrawing.moveSeam

theorem ContinuousPlanarPresentation.finiteNormalizedDrawing_correct
    {problem : PeriodicThreeDM} (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree)
    (zero : problem.ZeroOffsets) (bounds : presentation.drawing.SegmentEndpointsInExpandedSquare)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (simple : ∀ route∈presentation.drawing.edgeRoutes,LocalIncidenceDrawing.RouteIsSimple route) :
    (presentation.finiteNormalizedDrawing zero bounds).IsWellFormed ∧
    (presentation.finiteNormalizedDrawing zero bounds).VerticesSeparated ∧
    (presentation.finiteNormalizedDrawing zero bounds).BlankBoundary ∧
    ((presentation.finiteNormalizedDrawing zero bounds).HasOrientation ↔ problem.FiniteSatisfiable) := by
  let padded := presentation.finitePad zero bounds
  let strip := padded.toPlanarPresentation.stripNormalizedOrthogonalDrawing
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
  have stripWellFormed : strip.IsWellFormed := padded.stripNormalizedOrthogonalDrawing_isWellFormed
    wellFormed degree zero.isOneDimensional band paddedSeparated paddedSimple
  have stripSeparated : strip.VerticesSeparated :=
    padded.toPlanarPresentation.stripNormalizedOrthogonalDrawing_verticesSeparated
  have firstColumn : ∀ y,strip.get (0,y)=.blank :=
    padded.stripNormalizedOrthogonalDrawing_first_column_blank wellFormed degree zero inside
  have firstRow : ∀ x,strip.get (x,0)=.blank := by
    intro x
    exact ((PeriodicOrthogonalDrawing.blankVerticalBoundary_iff_rows strip).mp
      (padded.stripNormalizedOrthogonalDrawing_hasBlankVerticalBoundary
        wellFormed degree zero.isOneDimensional band) x).1
  refine ⟨strip.moveSeam_isWellFormed stripWellFormed,
    strip.moveSeam_verticesSeparated stripSeparated,
    strip.moveSeam_blankBoundary firstColumn firstRow,?_⟩
  change strip.moveSeam.HasOrientation ↔ problem.FiniteSatisfiable
  rw [strip.moveSeam_hasOrientation_iff stripWellFormed,
    padded.stripNormalizedOrthogonalDrawing_hasOrientation_iff_satisfiable
      wellFormed degree zero.isOneDimensional band paddedSeparated paddedSimple]
  exact (problem.finiteSatisfiable_iff zero).symm

/-- Cutting the normalized motif gives a finite region with exactly the
perfect-matchability of the original finite instance. -/
theorem ContinuousPlanarPresentation.finiteTrominoRegion_correct
    {problem : PeriodicThreeDM} (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree)
    (zero : problem.ZeroOffsets) (bounds : presentation.drawing.SegmentEndpointsInExpandedSquare)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (simple : ∀ route∈presentation.drawing.edgeRoutes,LocalIncidenceDrawing.RouteIsSimple route)
    (t : Tromino) :
    problem.FiniteSatisfiable ↔ t.Tileable
      (((presentation.finiteNormalizedDrawing zero bounds).expandedMotif t).toFinset : Set Cell) := by
  obtain ⟨drawingWellFormed,verticesSeparated,boundary,correct⟩ :=
    presentation.finiteNormalizedDrawing_correct wellFormed degree zero bounds separated simple
  exact correct.symm.trans (PeriodicOrthogonalDrawing.finiteSubstitution_correct t _
    drawingWellFormed verticesSeparated boundary)
end LeanTrominoes.PeriodicThreeDM
