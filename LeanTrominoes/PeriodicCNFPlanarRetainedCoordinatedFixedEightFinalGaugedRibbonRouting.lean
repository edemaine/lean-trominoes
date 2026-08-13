/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonFans
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedCoordinatedRouting

/-!
# Final gauged coordinated ribbon routing

This module specializes the padded normalized coordinated ribbon construction
to the completed retained, ordered, fixed-eight Figure 9 source.  All generic
source promises are supplied by the final gauged presentation, leaving a
single routing object parameterized only by the original periodic CNF and its
hardness-domain hypotheses.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

local instance finalGaugedRibbonRoutingVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- The exact positioned source routed by the final padded coordinated
ribbon construction. -/
noncomputable def retainedOrderedFixedEightFinalGaugedPaddedNormalizedSource
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :=
  PeriodicPlanarOneInThreeToThreeDM.normalizedPositionedSource
    ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).scale 2)
    ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
      source).scale 2)

set_option maxHeartbeats 1000000 in
/-- The concrete three-strand routing used by the hardness construction. -/
noncomputable def
    retainedOrderedFixedEightFinalGaugedPaddedCoordinatedRibbonRouting
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PeriodicPlanarOneInThreeToThreeDM.ThreeStrandRouting
      (retainedOrderedFixedEightFinalGaugedPaddedNormalizedSource
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).erase :=
  let presentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  PeriodicPlanarOneInThreeToThreeDM.paddedNormalizedCoordinatedRibbonThreeStrandRouting
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

set_option maxHeartbeats 2000000 in
/-- Distinct colored occurrence routes in the concrete final routing are
strictly separated. -/
theorem
    retainedOrderedFixedEightFinalGaugedPaddedCoordinatedRibbonRoutes_strictlyAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {first second :
      PeriodicPlanarOneInThreeToThreeDM.ActiveOccurrenceEntry
        (retainedOrderedFixedEightFinalGaugedPaddedNormalizedSource
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase}
    {firstColor secondColor : WireColor}
    (different :
      PeriodicPlanarOneInThreeToThreeDM.RibbonStrandsDifferent
        first firstColor second secondColor) :
    RoutesStrictlyAvoidEachOther
      ((retainedOrderedFixedEightFinalGaugedPaddedCoordinatedRibbonRouting
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).route first firstColor)
      ((retainedOrderedFixedEightFinalGaugedPaddedCoordinatedRibbonRouting
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).route second secondColor) := by
  let presentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  apply
    PeriodicPlanarOneInThreeToThreeDM.paddedNormalizedCoordinatedRibbonThreeStrandRoutes_strictlyAvoidEachOther
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
      different

end PeriodicOrthocrossing
end LeanTrominoes
