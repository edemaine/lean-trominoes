/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedElementDegrees
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonEraseBridge
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticDrawingWitness

/-! # Occurrence degree of the computed horizontal 3DM source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMTypedSourceComputed_occurrencesAtMostThree
    (source : PeriodicCNF Nat) :
    (horizontalThreeDMTypedSourceComputed source).OccurrencesAtMost 3 := by
  rw [horizontalThreeDMTypedSourceComputed,
    horizontalNormalizedRoutedEraseComputed_eq_semanticData]
  change
    (PeriodicPlanarOneInThreeToThreeDM.normalizedSource
      ((horizontalSemanticRoutedFormula source).scale 2)
      ((horizontalSemanticRoutedPlacement source).scale 2)).OccurrencesAtMost 3
  have certificate := horizontalSemanticDrawing_routingCertificate source
  have semanticOccurrences :=
    @PeriodicOneInThreePolarityNormalizationRouteSubdivision.CoordinatedAssemblyDrawingWitness.occurrences
      RoutedVariable horizontalRibbonRoutedVariableDecidableEq
      (horizontalSemanticRoutedFormula source)
      (horizontalSemanticRoutedPlacement source)
      (horizontalSemanticRoutedRibbonReadyPresentation source)
      (presentation source).drawing certificate
  have routedOccurrences :
      (horizontalSemanticRoutedFormula source).erase.OccurrencesAtMost 3 :=
    @PeriodicCNF.occurrencesAtMost_congr_beq RoutedVariable
      _
      (@instBEqOfDecidableEq RoutedVariable
        horizontalThreeDMTripleVariableDecidableEq)
      _
      (@instLawfulBEq RoutedVariable
        horizontalThreeDMTripleVariableDecidableEq)
      3 _
      semanticOccurrences
  have scaledOccurrences :
      ((horizontalSemanticRoutedFormula source).scale 2).erase.OccurrencesAtMost 3 := by
    simpa only [PositionedPeriodicCNF.erase_scale] using routedOccurrences
  rw [PeriodicPlanarOneInThreeToThreeDM.normalizedSource_eq]
  exact PeriodicCNF.anchorNormalize_occurrencesAtMost
    ((horizontalSemanticRoutedFormula source).scale 2).erase 3
    scaledOccurrences

end PeriodicCNFStripReduction
end LeanTrominoes
