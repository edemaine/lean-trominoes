/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedPlacementComputability
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRoutesComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionPlacementComputability

/-! # Computability of the retained routed-polarity placement -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

local instance retainedPolarityRoutedPlacementVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Proof-free placement after routed polarity normalization. -/
def retainedOrderedFixedEightPolarityNormalizedPlacementComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :=
  PeriodicOneInThreePolarityNormalizationRouteSubdivision.placement
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
      source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
      source)

theorem retainedOrderedFixedEightPolarityNormalizedPlacementComputed_period_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun source : PeriodicCNF Variable =>
      (retainedOrderedFixedEightPolarityNormalizedPlacementComputed
        source).period := by
  exact
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.placement_period_primrec
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement_period_primrec

theorem retainedOrderedFixedEightPolarityNormalizedPlacementComputed_position_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        PolarityNormalizedVariable
          (OneInThreeNoUnitVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)) =>
      (retainedOrderedFixedEightPolarityNormalizedPlacementComputed
        input.1).position input.2 := by
  exact
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.placement_position_primrec
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement_period_primrec
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement_position_primrec
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed_primrec

theorem retainedOrderedFixedEightPolarityNormalizedPlacementComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    retainedOrderedFixedEightPolarityNormalizedPlacementComputed source =
      PeriodicOneInThreePolarityNormalizationRouteSubdivision.placement
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) := by
  rw [
    retainedOrderedFixedEightPolarityNormalizedPlacementComputed,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty]

end PeriodicOrthocrossing
end LeanTrominoes
