/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanSelectionSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticPlanarPresentation

/-! # Semantic correctness of executable clause-fan activity -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseHasRightComputed_eq_semantic
    (source : PeriodicCNF Nat) (clauseIndex : Nat) :
    horizontalOccurrenceClauseHasRightComputed (source, clauseIndex) =
      (sourceClauseRibbonFanData
        (horizontalSemanticNormalizedPlanarPresentation source)
        clauseIndex).hasRight := by
  unfold horizontalOccurrenceClauseHasRightComputed
    sourceClauseRibbonFanData
  rw [horizontalOccurrenceClauseSelectedEntryComputed_eq_semantic]
  simp only [Option.isSome_map]
  exact List.isSome_find?_eq_any _ _

end PeriodicCNFStripReduction
end LeanTrominoes
