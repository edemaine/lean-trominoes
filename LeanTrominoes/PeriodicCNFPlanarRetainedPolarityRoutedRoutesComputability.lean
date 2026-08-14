/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedPolarityRoutedFormulaComputability
import LeanTrominoes.PeriodicCNFPlanarRetainedPolarityRoutedPlacementComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionIncidenceRoutesComputability

/-! # Computability of the retained routed-polarity routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

local instance retainedPolarityRoutedRoutesVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Proof-free final incidence-route family after routed polarity normalization. -/
def retainedOrderedFixedEightPolarityNormalizedIncidenceRoutesComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PeriodicOneInThreePolarityNormalizationRouteSubdivision.incidenceRoutes
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
      source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
      source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
      source)

theorem
    retainedOrderedFixedEightPolarityNormalizedIncidenceRoutesComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : (PeriodicCNF Variable × Nat) × Nat =>
      retainedOrderedFixedEightPolarityNormalizedIncidenceRoutesComputed
        input.1.1 input.1.2 input.2 := by
  exact
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.incidenceRoutes_primrec
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_primrec
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement_period_primrec
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed_primrec

theorem retainedOrderedFixedEightPolarityNormalizedIncidenceRoutesComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    retainedOrderedFixedEightPolarityNormalizedIncidenceRoutesComputed
        source =
      PeriodicOneInThreePolarityNormalizationRouteSubdivision.incidenceRoutes
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) := by
  rw [
    retainedOrderedFixedEightPolarityNormalizedIncidenceRoutesComputed,
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty]

end PeriodicOrthocrossing
end LeanTrominoes
