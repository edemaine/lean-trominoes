/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanEntriesSemanticBridge

/-! # Semantic correctness of executable clause-fan selection -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseSelectedEntryComputed_eq_semantic
    (source : PeriodicCNF Nat) (clauseIndex : Nat)
    (group : X3CClauseTerminalGroup) :
    horizontalOccurrenceClauseSelectedEntryComputed
        ((source, clauseIndex), group) =
      ((activeClauseOccurrenceEntries
        (horizontalSemanticNormalizedRibbonSource source).erase
        clauseIndex).find? fun entry =>
          decide
            (occurrenceClauseTerminalGroup
              (horizontalSemanticNormalizedRibbonSource source).erase
              entry = group)).map Subtype.val := by
  unfold horizontalOccurrenceClauseSelectedEntryComputed
  rw [horizontalOccurrenceClauseEntriesComputed_eq_semantic,
    List.find?_map_eq_map_find?]
  have predicatesEqual :
      (fun entry : ActiveOccurrenceEntry
          (horizontalSemanticNormalizedRibbonSource source).erase =>
        horizontalOccurrenceClauseEntryMatchesGroupComputed
          (((source, clauseIndex), group), entry.1)) =
        (fun entry =>
          decide
            (occurrenceClauseTerminalGroup
              (horizontalSemanticNormalizedRibbonSource source).erase
              entry = group)) := by
    funext entry
    unfold horizontalOccurrenceClauseEntryMatchesGroupComputed
      occurrenceClauseTerminalGroup
    rw [horizontalOccurrenceClauseEntryGroupComputed_eq_semantic]
  rw [predicatesEqual]

end PeriodicCNFStripReduction
end LeanTrominoes
