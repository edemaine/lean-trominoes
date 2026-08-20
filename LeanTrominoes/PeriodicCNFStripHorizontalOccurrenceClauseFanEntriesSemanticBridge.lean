/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanEntrySemanticBridge
import LeanTrominoes.ListAttachFilterMap

/-! # Proof erasure for executable clause-orbit occurrence lists -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseEntriesComputed_eq_semantic
    (source : PeriodicCNF Nat) (clauseIndex : Nat) :
    horizontalOccurrenceClauseEntriesComputed (source, clauseIndex) =
      (activeClauseOccurrenceEntries
        (horizontalSemanticNormalizedRibbonSource source).erase
        clauseIndex).map Subtype.val := by
  unfold horizontalOccurrenceClauseEntriesComputed
  rw [horizontalOccurrenceClauseSourceComputed_eq_semantic]
  simp_rw [horizontalOccurrenceClauseEntryClauseIndexComputed_eq_semantic]
  unfold activeClauseOccurrenceEntries
  exact List.filterMap_if_some_eq_map_attach_filter _ _

end PeriodicCNFStripReduction
end LeanTrominoes
