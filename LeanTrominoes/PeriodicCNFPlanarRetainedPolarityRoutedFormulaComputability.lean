/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedPlacementComputability
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRoutesComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionFormulaComputability

/-! # Computability of the retained routed-polarity formula -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

local instance retainedPolarityRoutedFormulaVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Proof-free positioned formula after routed polarity normalization. -/
def retainedOrderedFixedEightPolarityNormalizedPositionedFormulaComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :=
  PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
      source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
      source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
      source)

theorem
    retainedOrderedFixedEightPolarityNormalizedPositionedFormulaComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedOrderedFixedEightPolarityNormalizedPositionedFormulaComputed :
        PeriodicCNF Variable → _) := by
  exact
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula_primrec
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_primrec
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement_period_primrec
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed_primrec

theorem
    retainedOrderedFixedEightPolarityNormalizedPositionedFormulaComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    retainedOrderedFixedEightPolarityNormalizedPositionedFormulaComputed
        source =
      PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) := by
  rw [
    retainedOrderedFixedEightPolarityNormalizedPositionedFormulaComputed,
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty]

end PeriodicOrthocrossing
end LeanTrominoes
