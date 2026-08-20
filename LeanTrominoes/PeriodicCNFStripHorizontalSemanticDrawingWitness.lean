/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRibbonSemanticData
import LeanTrominoes.PeriodicCNFStripPlanarReduction
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRibbonThreeDMDrawingWitness

/-! # Coordinated-routing witness behind the horizontal semantic drawing -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The existing proof-backed horizontal presentation exposes exactly the
coordinated assembly whose finite data are enumerated by the executable
compiler.  Its expensive structural certificates remain packaged opaquely. -/
theorem horizontalSemanticDrawing_routingCertificate
    (source : PeriodicCNF Nat) :
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.CoordinatedAssemblyDrawingWitness
      (horizontalSemanticRoutedFormula source)
      (horizontalSemanticRoutedPlacement source)
      (horizontalSemanticRoutedRibbonReadyPresentation source)
      (presentation source).drawing := by
  let base := horizontalSemanticFinalGaugedPresentation source
  have certificate :=
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMContinuousPlanarPresentation_drawing_certificate
      base.toHaloBoundedRibbonReadyIncidencePresentation base.unitSteps
      (PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_allAtomsNodup
        (sourceFormula source)
        (sourceFormula_isLocal source)
        (sourceFormula_widthAtMostThree source)
        (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
        (sourceFormula_clausesNonempty source))
      (PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_occurrencesAtMostThree
        (sourceFormula source)
        (sourceFormula_isLocal source)
        (sourceFormula_widthAtMostThree source)
        (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
        (sourceFormula_clausesNonempty source)).occurrencesAtMostThree
      (PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
        (sourceFormula source)
        (sourceFormula_isLocal source)
        (sourceFormula_widthAtMostThree source)
        (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
        (sourceFormula_clausesNonempty source))
      base.variableRoutesInOccurrenceOrder
      base.ternaryClauseRoutesInClockwiseOrder
  simpa only [
    base,
    horizontalSemanticFinalGaugedPresentation,
    horizontalSemanticRoutedFormula,
    horizontalSemanticRoutedPlacement,
    horizontalSemanticRoutedRoutes,
    horizontalSemanticRoutedRibbonReadyPresentation,
    horizontalFormula,
    horizontalPlacement,
    horizontalRoutes,
    presentation,
    PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation]
    using certificate

end PeriodicCNFStripReduction
end LeanTrominoes
