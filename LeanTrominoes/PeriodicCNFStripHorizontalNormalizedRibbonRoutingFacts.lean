/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticDrawingWitness
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticPlanarPresentation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonFanCompatibilityTransport
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedCoordinatedRouting

/-! # Structural facts for the normalized horizontal ribbon source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The concrete doubled and normalized horizontal source still has clause
width at most three. -/
theorem horizontalSemanticNormalizedRibbonSource_widthAtMostThree
    (source : PeriodicCNF Nat) :
    (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3 := by
  let certificate := horizontalSemanticDrawing_routingCertificate source
  have width := paddedNormalizedSource_widthAtMostThree
    (source := horizontalSemanticRoutedFormula source)
    (placement := horizontalSemanticRoutedPlacement source)
    certificate.width
  simpa only [horizontalSemanticNormalizedRibbonSource] using width

/-- The finite variable and clause fan tables of the concrete normalized
horizontal source are clockwise compatible. -/
theorem horizontalSemanticNormalizedRibbonSource_fansCompatible
    (source : PeriodicCNF Nat) :
    SourceRibbonFansClockwiseCompatible
      (horizontalSemanticNormalizedPlanarPresentation source) := by
  unfold horizontalRibbonRoutedVariableDecidableEq
  let certificate := horizontalSemanticDrawing_routingCertificate source
  have compatible :=
    paddedNormalizedRibbonReady_sourceRibbonFansClockwiseCompatible
      (horizontalSemanticRoutedRibbonReadyPresentation source)
      certificate.width certificate.occurrences certificate.arity
      certificate.variableOrdered certificate.clauseOrdered
  simpa only [horizontalSemanticNormalizedPlanarPresentation,
    horizontalSemanticNormalizedRibbonReadyPresentation,
    horizontalSemanticNormalizedRibbonSource,
    horizontalSemanticFinalGaugedPresentation,
    horizontalSemanticRoutedFormula,
    horizontalSemanticRoutedPlacement,
    horizontalFormula,
    horizontalPlacement,
    horizontalRoutes] using compatible

end PeriodicCNFStripReduction
end LeanTrominoes

end
