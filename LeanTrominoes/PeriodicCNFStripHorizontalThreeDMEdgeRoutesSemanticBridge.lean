/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteAtTagSemanticBridge

/-! # Semantic bridge for complete stored horizontal edge routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalThreeDMProblemComputed_eq_semantic
    (source : PeriodicCNF Nat) :
    horizontalThreeDMProblemComputed source =
      @encodedProblem RoutedVariable
        horizontalRibbonRoutedVariableDecidableEq
        (horizontalSemanticNormalizedRibbonSource source).erase := by
  unfold horizontalThreeDMProblemComputed
  rw [horizontalNormalizedRoutedEraseComputed_eq_semanticData]

theorem horizontalThreeDMIncidenceTagsComputed_eq_semantic
    (source : PeriodicCNF Nat) :
    horizontalThreeDMIncidenceTagsComputed source =
      PeriodicThreeDM.incidenceTags
        (@encodedProblem RoutedVariable
        horizontalRibbonRoutedVariableDecidableEq
        (horizontalSemanticNormalizedRibbonSource source).erase) := by
  unfold horizontalThreeDMIncidenceTagsComputed
  rw [horizontalThreeDMProblemComputed_eq_semantic]

theorem horizontalThreeDMEdgeRoutesComputed_eq_assembled
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation)) :
    horizontalThreeDMEdgeRoutesComputed source =
      @assembledEdgeRoutes
        RoutedVariable horizontalRibbonRoutedVariableDecidableEq
        (horizontalSemanticNormalizedRibbonSource source).erase
        (coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible) := by
  unfold horizontalThreeDMEdgeRoutesComputed assembledEdgeRoutes
  rw [horizontalThreeDMIncidenceTagsComputed_eq_semantic]
  apply List.map_congr_left
  intro tag tagMember
  exact horizontalAssembledRouteAtTagComputed_eq_semantic
    source width compatible tag

end PeriodicCNFStripReduction
end LeanTrominoes
