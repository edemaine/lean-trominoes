/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalClauseIncomingDirectionBlocks
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonRoutingFacts
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedFormulaSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRoutesSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticPlanarPresentationRoutes

/-! # Horizontal semantic clause fans from their stored direction blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open HorizontalRoutedRouteHeaderClauseFrame

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The occurrence-three certificate is preserved by padding and the clause
anchor normalization used by the semantic ribbon presentation. -/
theorem horizontalSemanticNormalizedRibbonSource_occurrencesAtMostThree
    (source : PeriodicCNF Nat) :
    @PeriodicCNF.OccurrencesAtMost RoutedVariable
      (@instBEqOfDecidableEq RoutedVariable horizontalRibbonRoutedVariableDecidableEq)
      (by infer_instance) 3 (horizontalSemanticNormalizedRibbonSource source).erase := by
  have certificate := horizontalSemanticDrawing_routingCertificate source
  have occurrences :=
    @PeriodicOneInThreePolarityNormalizationRouteSubdivision.CoordinatedAssemblyDrawingWitness.occurrences
      RoutedVariable horizontalRibbonRoutedVariableDecidableEq
      (horizontalSemanticRoutedFormula source)
      (horizontalSemanticRoutedPlacement source)
      (horizontalSemanticRoutedRibbonReadyPresentation source)
      (presentation source).drawing certificate
  exact normalizedSource_occurrencesAtMost
    ((horizontalSemanticRoutedFormula source).scale 2)
    ((horizontalSemanticRoutedPlacement source).scale 2)
    (by simpa only [PositionedPeriodicCNF.erase_scale] using occurrences)

/-- The executable horizontal clause fans are precisely the fans assembled
from the incoming direction blocks of the original unpadded stored routes. -/
theorem horizontalClauseIncomingDirectionBlocks_fans_eq_computed
    (source : PeriodicCNF Nat) :
    (clauseIncomingDirectionBlocks (horizontalRoutedFormulaComputed source)
        (horizontalRoutedRoutesComputed source)).map fanOfDirections =
      (List.range (horizontalRoutedFormulaComputed source).clauses.length).map
        (fun index => horizontalOccurrenceClauseRibbonFanDataComputed (source, index)) := by
  rw [horizontalRoutedFormulaComputed_eq_semanticData,
    horizontalRoutedRoutesComputed_eq_semanticData]
  have blocks := clauseIncomingDirectionBlocks_normalized_scale
    (horizontalSemanticRoutedFormula source) (horizontalSemanticRoutedPlacement source)
    (horizontalSemanticRoutedRoutes source) 2 (by decide)
  have fanEq := clauseIncomingDirectionBlocks_fans_eq_source_range
    (horizontalSemanticNormalizedPlanarPresentation source)
    (horizontalSemanticNormalizedRibbonSource_widthAtMostThree source)
    (horizontalSemanticNormalizedRibbonSource_occurrencesAtMostThree source)
  rw [horizontalSemanticNormalizedPlanarPresentation_routes] at fanEq
  change (clauseIncomingDirectionBlocks
      (normalizedPositionedSource ((horizontalSemanticRoutedFormula source).scale 2)
        ((horizontalSemanticRoutedPlacement source).scale 2)) _).map _ = _ at fanEq
  rw [blocks] at fanEq
  have count : (horizontalSemanticNormalizedRibbonSource source).clauses.length =
      (horizontalSemanticRoutedFormula source).clauses.length := by
    simp only [horizontalSemanticNormalizedRibbonSource, normalizedPositionedSource,
      PositionedPeriodicCNF.anchorNormalize, PositionedPeriodicCNF.scale_clauses,
      List.length_map]
  rw [count] at fanEq
  simpa only [horizontalOccurrenceClauseRibbonFanDataComputed_eq_semantic] using fanEq

end LeanTrominoes.PeriodicCNFStripReduction

end
