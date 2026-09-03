/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileFigureNineTernaryTailValues
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceCorrect
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalClauseOrdering
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedDrawing
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedClauseRouteOrder
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineSemantics
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationClauseOrderingArity
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationVariableGaugeArity

/-! # Clause arities through retained final clockwise ordering -/

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicOrthocrossing

open PeriodicCNF

/-- Every ternary clause at the retained unit-free endpoint has equal
polarities in its final two positions. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_ternaryTailValuesEqual
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    PeriodicOneInThreePolarityNormalization.TernaryTailValuesEqual
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source) := by
  let sourceProfiles :=
    PeriodicCNF.FormulaShape.clauseProfiles
      (PeriodicCNF.FormulaShapeRetainedFigureNineSource.shape source)
  have sourceCorrect :
      sourceProfiles.map
          PeriodicCNF.UnaryProgramClauseProfile.ClauseProfile.literals =
        (retainedFigureNineClearancePositionedFormula
          source).erase.clauses.map
            PeriodicCNF.ClauseProfileOccurrenceSplit.literalProfiles := by
    exact (PeriodicCNF.FormulaShapeRetainedFigureNineSource.correct
      source sourceWidth sourceClausesNonempty).1
  have logicalTailValues :=
    PeriodicCNF.ClauseProfileFigureNine.formula_ternaryTailValuesEqual
      (retainedFigureNineClearancePositionedFormula source).erase
      sourceProfiles sourceCorrect
  apply
    PeriodicOneInThreePolarityNormalization.ternaryTailValuesEqual_of_erase
  rw [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase]
  exact logicalTailValues

/-- The last clockwise sort preserves the complete polarity-normalized
clause-arity sequence of the retained unit-free endpoint. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula_polarityClauseLengths_eq_raw
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    (PeriodicOneInThreePolarityNormalization.formula
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).erase).clauses.map List.length =
      (PeriodicOneInThreePolarityNormalization.formula
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase).clauses.map List.length := by
  simpa only [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula]
    using
      PeriodicOneInThreePolarityNormalization.formula_clauseLengths_orderClausesByRouteDirection
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_arityTwoOrThree
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_ternaryClauseRoutesInUnitEliminationOrder
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_ternaryTailValuesEqual
          source sourceWidth sourceClausesNonempty)

/-- The final canonical variable gauge changes offsets but preserves the
complete polarity-normalized clause-arity sequence. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_polarityClauseLengths_eq_raw
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    (PeriodicOneInThreePolarityNormalization.formula
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).erase).clauses.map List.length =
      (PeriodicOneInThreePolarityNormalization.formula
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase).clauses.map List.length := by
  rw [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula,
    PositionedPeriodicCNF.erase_variableGauge,
    PeriodicOneInThreePolarityNormalization.formula_variableGauge_clauseLengths]
  exact
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula_polarityClauseLengths_eq_raw
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty

end LeanTrominoes.PeriodicOrthocrossing
