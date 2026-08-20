/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableStubSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRibbonCorridorSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseStubSemanticBridge

/-! # Semantic correctness of complete coordinated occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceCoordinatedRouteComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    horizontalOccurrenceCoordinatedRouteComputed
        (((source, entry.1.1), entry.1.2), color) =
      joinAtEndpoint
        (joinAtEndpoint
          (occurrenceCoordinatedRibbonVariableStub
            (horizontalSemanticNormalizedPlanarPresentation source)
            entry color)
          (occurrenceRibbonCorridorCore
            (horizontalSemanticNormalizedPlanarPresentation source)
            entry color))
        (occurrenceCoordinatedRibbonClauseStub
          (horizontalSemanticNormalizedPlanarPresentation source)
          entry color) := by
  unfold horizontalOccurrenceCoordinatedRouteComputed
  rw [horizontalOccurrenceVariableStubComputed_eq_semantic,
    horizontalOccurrenceRibbonCorridorCoreComputed_eq_semantic,
    horizontalOccurrenceClauseStubComputed_eq_semantic]

end PeriodicCNFStripReduction
end LeanTrominoes
