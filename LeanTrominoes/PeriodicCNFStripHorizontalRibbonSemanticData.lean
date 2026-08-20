/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalEncoderData
import LeanTrominoes.PeriodicCNFStripHorizontalRibbonInstances
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRibbonReadyPresentation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalized

/-! # Named semantic ribbon source for the horizontal reduction -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Positioned formula after routed polarity normalization, before padding. -/
def horizontalSemanticRoutedFormula (source : PeriodicCNF Nat) :=
  PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula
    (PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source))
    (PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
      (sourceFormula source))
    (horizontalRoutes source)

/-- Matching routed placement before padding. -/
def horizontalSemanticRoutedPlacement (source : PeriodicCNF Nat) :=
  PeriodicOneInThreePolarityNormalizationRouteSubdivision.placement
    (PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
      (sourceFormula source))
    (horizontalRoutes source)

/-- Matching routed incidence family before padding. -/
def horizontalSemanticRoutedRoutes (source : PeriodicCNF Nat) :=
  PeriodicOneInThreePolarityNormalizationRouteSubdivision.incidenceRoutes
    (PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source))
    (PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
      (sourceFormula source))
    (horizontalRoutes source)

/-- Ribbon-ready presentation after routed polarity normalization. -/
def horizontalSemanticRoutedRibbonReadyPresentation
    (source : PeriodicCNF Nat) :=
  let base :=
    PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)
  PeriodicOneInThreePolarityNormalizationRouteSubdivision.haloBoundedRibbonReadyPresentation
    base.toHaloBoundedRibbonReadyIncidencePresentation base.unitSteps

/-- Final doubled, anchor-normalized positioned source. -/
def horizontalSemanticNormalizedRibbonSource (source : PeriodicCNF Nat) :=
  PeriodicPlanarOneInThreeToThreeDM.normalizedPositionedSource
    ((horizontalSemanticRoutedFormula source).scale 2)
    ((horizontalSemanticRoutedPlacement source).scale 2)

/-- Final source presentation from which the macrocell ribbon routes are
assembled. -/
def horizontalSemanticNormalizedRibbonReadyPresentation
    (source : PeriodicCNF Nat) :=
  PeriodicPlanarOneInThreeToThreeDM.normalizedRibbonReadyIncidencePresentation
    (horizontalSemanticRoutedRibbonReadyPresentation source).scaleTwo

/-- Choice-backed occurrence source-route function with its active-entry
domain inferred directly from the semantic presentation. -/
def horizontalSemanticOccurrenceSourceRouteFunction
    (source : PeriodicCNF Nat) :=
  fun entry =>
    PeriodicPlanarOneInThreeToThreeDM.occurrenceSourceRoute
      (horizontalSemanticNormalizedRibbonReadyPresentation source
        |>.toPlanarIncidencePresentation)
      entry

end PeriodicCNFStripReduction
end LeanTrominoes
