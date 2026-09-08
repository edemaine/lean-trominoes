/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonSourceBridge

/-! # Executable clause index and terminal group of the same tagged occurrence -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Executable occurrence lookup agrees with a tagged lookup in the actual
semantic normalized source. -/
theorem horizontalOccurrenceLookupComputed_eq_of_semanticLookup
    (source : PeriodicCNF Nat) (atom : RoutedVariable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence RoutedVariable)
    (lookup : occurrenceAt (horizontalSemanticNormalizedRibbonSource source).erase atom slot = some tagged) :
    horizontalOccurrenceLookupComputed ((source, atom), slot) = some tagged := by
  unfold horizontalOccurrenceLookupComputed horizontalOccurrenceLookupInput
  rw [horizontalNormalizedRoutedFormulaComputed_eq_semanticData]
  exact lookup

/-- A successful executable lookup fixes the clause index of the actual
selected occurrence, without a separate search. -/
theorem horizontalOccurrenceClauseIndexComputed_eq_of_lookup
    (input : HorizontalOccurrenceRouteInput) (tagged : TaggedOccurrence RoutedVariable)
    (lookup : horizontalOccurrenceLookupComputed input = some tagged) :
    horizontalOccurrenceClauseIndexComputed input = tagged.2.1 := by
  rcases input with ⟨⟨source, atom⟩, slot⟩
  simp only [horizontalOccurrenceClauseIndexComputed,
    horizontalOccurrenceClauseFanEntryInputComputed,
    horizontalOccurrenceClauseEntryClauseIndexComputed,
    horizontalOccurrenceClauseEntryLookupComputed,
    horizontalOccurrenceClauseEntryQueryComputed, lookup]

/-- The physical terminal group comes from that same tagged literal index. -/
theorem horizontalOccurrenceClauseTerminalGroupComputed_eq_of_lookup
    (input : HorizontalOccurrenceRouteInput) (tagged : TaggedOccurrence RoutedVariable)
    (lookup : horizontalOccurrenceLookupComputed input = some tagged) :
    horizontalOccurrenceClauseTerminalGroupComputed input = terminalGroupOfLiteralIndex tagged.2.2 := by
  rcases input with ⟨⟨source, atom⟩, slot⟩
  simp only [horizontalOccurrenceClauseTerminalGroupComputed,
    horizontalOccurrenceClauseFanEntryInputComputed,
    horizontalOccurrenceClauseEntryGroupComputed,
    horizontalOccurrenceClauseEntryLiteralIndexComputed,
    horizontalOccurrenceClauseEntryLookupComputed,
    horizontalOccurrenceClauseEntryQueryComputed, lookup]

end LeanTrominoes.PeriodicCNFStripReduction

end
