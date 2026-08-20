/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRoutingSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableStubSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableOriginComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMClauseOriginData
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonSourceBridge

/-! # Computed horizontal gadget origins agree with certified routing -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalThreeDMVariableOriginComputed_eq_routing
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation))
    (atom : RoutedVariable) :
    horizontalThreeDMVariableOriginComputed source atom =
      (coordinatedSourceRibbonThreeStrandRouting
        (horizontalSemanticNormalizedRibbonReadyPresentation source)
        width compatible).variableOrigin atom := by
  unfold horizontalThreeDMVariableOriginComputed
  rw [horizontalPaddedRoutedPositionComputed_eq_semantic]
  rfl

theorem horizontalThreeDMClauseOriginComputed_eq_routing
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation))
    (clauseIndex : Nat) :
    horizontalThreeDMClauseOriginComputed source clauseIndex =
      (coordinatedSourceRibbonThreeStrandRouting
        (horizontalSemanticNormalizedRibbonReadyPresentation source)
        width compatible).clauseOrigin clauseIndex := by
  unfold horizontalThreeDMClauseOriginComputed
    horizontalNormalizedRoutedClausePositionComputed
  rw [horizontalNormalizedRoutedFormulaComputed_eq_semanticData]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes
