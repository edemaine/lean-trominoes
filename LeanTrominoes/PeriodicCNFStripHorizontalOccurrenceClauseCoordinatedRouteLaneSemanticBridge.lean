/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteMetadataSemanticBridge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseLane

/-! # Semantic correctness of clause coordinated-route lanes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceRibbonLaneComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    horizontalOccurrenceRibbonLaneComputed
        (((source, entry.1.1), entry.1.2), color) =
      routedRibbonLane
        (horizontalSemanticNormalizedRibbonSource source).erase
        entry color := by
  unfold horizontalOccurrenceRibbonLaneComputed
    horizontalOccurrenceRibbonLaneInputComputed
  rw [horizontalOccurrenceClauseTerminalGroupComputed_eq_semantic]
  rw [routedRibbonLane_eq_clauseTerminalGroup]

end PeriodicCNFStripReduction
end LeanTrominoes
