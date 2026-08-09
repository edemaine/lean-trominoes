import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonRouting
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineThreeDM
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedContinuousPresentation

/-!
# Continuously planar 3DM endpoint of the final Figure 9 routing

This module packages the concrete retained, ordered, fixed-eight, gauged
ribbon construction as the continuously planar periodic 3DM instance used by
the hardness pipeline.  It also records the instance's degree promise and
semantic equivalence to the original local periodic CNF.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open Gadget

set_option maxHeartbeats 2000000

local instance finalGaugedRibbonThreeDMVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- The exact natural-number periodic 3DM problem drawn by the final padded
coordinated ribbon routing. -/
noncomputable def retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PeriodicThreeDM :=
  PeriodicPlanarOneInThreeToThreeDM.encodedProblem
    (retainedOrderedFixedEightFinalGaugedPaddedNormalizedSource
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).erase

/-- The final retained Figure 9 3DM problem has a concrete continuously
planar presentation, with no geometric premise left to discharge. -/
noncomputable def
    retainedOrderedFixedEightFinalGaugedPaddedContinuousPlanarPresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).ContinuousPlanarPresentation := by
  let presentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  exact
    PeriodicPlanarOneInThreeToThreeDM.paddedNormalizedCoordinatedContinuousPlanarPresentation
      presentation.toHaloBoundedRibbonReadyIncidencePresentation
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_widthAtMostThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_occurrencesAtMostThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).occurrencesAtMostThree
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      presentation.variableRoutesInOccurrenceOrder
      presentation.ternaryClauseRoutesInClockwiseOrder

/-- Every colored element of the final continuously planar 3DM instance has
degree two or three. -/
theorem retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem_degreeTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).DegreeTwoOrThree := by
  let finalSource :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let finalPlacement :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
      source
  have occurrences :=
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_occurrencesAtMostThree
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).occurrencesAtMostThree
  have arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree finalSource.erase :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  change
    (PeriodicPlanarOneInThreeToThreeDM.normalizedProblem
      (finalSource.scale 2) (finalPlacement.scale 2)).DegreeTwoOrThree
  exact
    PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_degreeTwoOrThree
      (finalSource.scale 2) (finalPlacement.scale 2)
      (by simpa using occurrences) (by simpa using arity)

/-- The final continuously planar 3DM instance has a perfect matching exactly
when the original periodic CNF is satisfiable. -/
theorem retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).Satisfiable ↔ source.Satisfiable := by
  let finalSource :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let finalPlacement :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
      source
  have occurrences :=
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_occurrencesAtMostThree
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).occurrencesAtMostThree
  have arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree finalSource.erase :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have normalizedIff :=
    PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_satisfiable_iff_source
      (finalSource.scale 2) (finalPlacement.scale 2)
      (by simpa using occurrences) (by simpa using arity)
  have finalIff :
      PeriodicOneInThree.Satisfiable finalSource.erase ↔
        PeriodicOneInThree.Satisfiable
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).erase :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_satisfiable_iff
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have normalizedIff' :
      (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).Satisfiable ↔
        PeriodicOneInThree.Satisfiable finalSource.erase := by
    simpa [finalSource, finalPlacement,
      retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem,
      retainedOrderedFixedEightFinalGaugedPaddedNormalizedSource,
      PeriodicPlanarOneInThreeToThreeDM.normalizedProblem,
      PeriodicPlanarOneInThreeToThreeDM.normalizedSource,
      PositionedPeriodicCNF.erase_scale] using normalizedIff
  exact
    normalizedIff'.trans
      (finalIff.trans
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_satisfiable_iff
          source sourceLocal sourceWidth sourceOccurrences))

/-- The equivalent abstract trichromatic graph-orientation statement for the
final continuously planar endpoint. -/
theorem retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem_graphHasOrientation_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).GraphHasOrientation ↔ source.Satisfiable := by
  exact
    (PeriodicThreeDM.satisfiable_iff_graphHasOrientation
      (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)).symm.trans
      (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem_satisfiable_iff
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes
