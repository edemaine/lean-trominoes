/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableStubData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableCoordinatedRouteSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementSemanticBridge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoordinatedStubs

/-! # Semantic correctness of translated variable occurrence stubs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalPaddedRoutedPositionComputed_eq_semantic
    (source : PeriodicCNF Nat) (atom : RoutedVariable) :
    horizontalPaddedRoutedPositionComputed source atom =
      ((horizontalSemanticRoutedPlacement source).scale 2).position atom := by
  unfold horizontalPaddedRoutedPositionComputed
  rw [horizontalRoutedPlacementComputed_eq_semanticData]
  rfl

theorem horizontalOccurrenceVariableStubComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    horizontalOccurrenceVariableStubComputed
        (((source, entry.1.1), entry.1.2), color) =
      occurrenceCoordinatedRibbonVariableStub
        (horizontalSemanticNormalizedPlanarPresentation source)
        entry color := by
  unfold horizontalOccurrenceVariableStubComputed
    occurrenceCoordinatedRibbonVariableStub
  rw [horizontalPaddedRoutedPositionComputed_eq_semantic,
    horizontalOccurrenceVariableCoordinatedRouteComputed_eq_semantic]

end PeriodicCNFStripReduction
end LeanTrominoes
