/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanData
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonEraseBridge

/-! # Semantic bridge for clause-fan occurrence lookup -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseSourceComputed_eq_semantic
    (source : PeriodicCNF Nat) (clauseIndex : Nat) :
    horizontalOccurrenceClauseSourceComputed (source, clauseIndex) =
      (horizontalSemanticNormalizedRibbonSource source).erase := by
  exact horizontalNormalizedRoutedEraseComputed_eq_semanticData source

theorem horizontalOccurrenceClauseEntryLookupComputed_eq_semantic
    (source : PeriodicCNF Nat) (clauseIndex : Nat)
    (entry : HorizontalClauseOccurrenceEntry) :
    horizontalOccurrenceClauseEntryLookupComputed
        ((source, clauseIndex), entry) =
      occurrenceAt
        (horizontalSemanticNormalizedRibbonSource source).erase
        entry.1 entry.2 := by
  unfold horizontalOccurrenceClauseEntryLookupComputed
    horizontalOccurrenceClauseEntryQueryComputed
    horizontalOccurrenceLookupComputed horizontalOccurrenceLookupInput
  rw [horizontalNormalizedRoutedEraseComputed_eq_semanticData]

end PeriodicCNFStripReduction
end LeanTrominoes
