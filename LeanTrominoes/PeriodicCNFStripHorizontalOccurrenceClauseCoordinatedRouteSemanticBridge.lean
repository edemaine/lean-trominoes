/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteLaneSemanticBridge

/-! # Semantic correctness of clause-side coordinated routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseCoordinatedRouteComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    horizontalOccurrenceClauseCoordinatedRouteComputed
        (((source, entry.1.1), entry.1.2), color) =
      (sourceClauseRibbonFanData
        (horizontalSemanticNormalizedPlanarPresentation source)
        (occurrenceClauseIndex
          (horizontalSemanticNormalizedRibbonSource source).erase
          entry.1.1 entry.1.2)).coordinatedRoute
        (occurrenceClauseTerminalGroup
          (horizontalSemanticNormalizedRibbonSource source).erase entry)
        (routedRibbonLane
          (horizontalSemanticNormalizedRibbonSource source).erase
          entry color) := by
  unfold horizontalOccurrenceClauseCoordinatedRouteComputed
    horizontalOccurrenceClauseCoordinatedRouteInputComputed
    horizontalOccurrenceClauseRibbonFanQueryComputed
  rw [horizontalOccurrenceClauseRibbonFanDataComputed_eq_semantic,
    horizontalOccurrenceClauseIndexComputed_eq_semantic,
    horizontalOccurrenceClauseTerminalGroupComputed_eq_semantic,
    horizontalOccurrenceRibbonLaneComputed_eq_semantic]

end PeriodicCNFStripReduction
end LeanTrominoes
