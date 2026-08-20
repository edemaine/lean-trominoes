/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanEntrySemanticBridge

/-! # Semantic correctness of clause coordinated-route metadata -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseIndexComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase) :
    horizontalOccurrenceClauseIndexComputed
        ((source, entry.1.1), entry.1.2) =
      occurrenceClauseIndex
        (horizontalSemanticNormalizedRibbonSource source).erase
        entry.1.1 entry.1.2 := by
  unfold horizontalOccurrenceClauseIndexComputed
    horizontalOccurrenceClauseFanEntryInputComputed
  exact
    horizontalOccurrenceClauseEntryClauseIndexComputed_eq_semantic
      source 0 entry.1

theorem horizontalOccurrenceClauseTerminalGroupComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase) :
    horizontalOccurrenceClauseTerminalGroupComputed
        ((source, entry.1.1), entry.1.2) =
      occurrenceClauseTerminalGroup
        (horizontalSemanticNormalizedRibbonSource source).erase entry := by
  unfold horizontalOccurrenceClauseTerminalGroupComputed
    horizontalOccurrenceClauseFanEntryInputComputed
    occurrenceClauseTerminalGroup
  exact horizontalOccurrenceClauseEntryGroupComputed_eq_semantic
    source 0 entry.1

end PeriodicCNFStripReduction
end LeanTrominoes
