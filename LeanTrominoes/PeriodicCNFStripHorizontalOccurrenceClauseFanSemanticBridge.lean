/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanDataProjections
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanHasRightSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanDirectionSemanticBridge

/-! # Semantic correctness of executable horizontal clause-fan data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseRibbonFanDataComputed_eq_semantic
    (source : PeriodicCNF Nat) (clauseIndex : Nat) :
    horizontalOccurrenceClauseRibbonFanDataComputed
        (source, clauseIndex) =
      sourceClauseRibbonFanData
        (horizontalSemanticNormalizedPlanarPresentation source)
        clauseIndex := by
  apply ClauseRibbonFanData.ext_fields
  · rw [horizontalOccurrenceClauseRibbonFanDataComputed_hasRight]
    exact horizontalOccurrenceClauseHasRightComputed_eq_semantic
      source clauseIndex
  · intro group
    rw [horizontalOccurrenceClauseRibbonFanDataComputed_direction]
    exact horizontalOccurrenceClauseDirectionComputed_eq_semantic
      source clauseIndex group

end PeriodicCNFStripReduction
end LeanTrominoes
