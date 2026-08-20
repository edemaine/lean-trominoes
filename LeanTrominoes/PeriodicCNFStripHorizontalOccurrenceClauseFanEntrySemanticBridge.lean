/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanLookupSemanticBridge

/-! # Semantic metadata of executable clause-fan entries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseEntryClauseIndexComputed_eq_semantic
    (source : PeriodicCNF Nat) (clauseIndex : Nat)
    (entry : HorizontalClauseOccurrenceEntry) :
    horizontalOccurrenceClauseEntryClauseIndexComputed
        ((source, clauseIndex), entry) =
      occurrenceClauseIndex
        (horizontalSemanticNormalizedRibbonSource source).erase
        entry.1 entry.2 := by
  unfold horizontalOccurrenceClauseEntryClauseIndexComputed
    occurrenceClauseIndex
  rw [horizontalOccurrenceClauseEntryLookupComputed_eq_semantic]
  generalize occurrenceAt
      (horizontalSemanticNormalizedRibbonSource source).erase
      entry.1 entry.2 = result
  cases result <;> rfl

theorem horizontalOccurrenceClauseEntryLiteralIndexComputed_eq_semantic
    (source : PeriodicCNF Nat) (clauseIndex : Nat)
    (entry : HorizontalClauseOccurrenceEntry) :
    horizontalOccurrenceClauseEntryLiteralIndexComputed
        ((source, clauseIndex), entry) =
      occurrenceLiteralIndex
        (horizontalSemanticNormalizedRibbonSource source).erase
        entry.1 entry.2 := by
  unfold horizontalOccurrenceClauseEntryLiteralIndexComputed
    occurrenceLiteralIndex
  rw [horizontalOccurrenceClauseEntryLookupComputed_eq_semantic]
  generalize occurrenceAt
      (horizontalSemanticNormalizedRibbonSource source).erase
      entry.1 entry.2 = result
  cases result <;> rfl

theorem horizontalOccurrenceClauseEntryGroupComputed_eq_semantic
    (source : PeriodicCNF Nat) (clauseIndex : Nat)
    (entry : HorizontalClauseOccurrenceEntry) :
    horizontalOccurrenceClauseEntryGroupComputed
        ((source, clauseIndex), entry) =
      terminalGroupOfLiteralIndex
        (occurrenceLiteralIndex
          (horizontalSemanticNormalizedRibbonSource source).erase
          entry.1 entry.2) := by
  unfold horizontalOccurrenceClauseEntryGroupComputed
  rw [horizontalOccurrenceClauseEntryLiteralIndexComputed_eq_semantic]

end PeriodicCNFStripReduction
end LeanTrominoes
