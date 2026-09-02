/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceDirectionCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceDirectionSemantics

/-! # Semantics of final clause-incidence direction blocks -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

@[simp] theorem finalClauseIncidenceQueryBlock_length
    (fan : ClauseRibbonFanData) :
    (finalClauseIncidenceQueryBlock fan).length = 27 := by
  simp [finalClauseIncidenceQueryBlock,
    PeriodicPlanarOneInThreeToThreeDM.allClauseSets]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

@[simp] theorem directSourceFinalClauseIncidenceQueries_length
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseIncidenceQueries decider symbols).length =
      27 * (directSourceFinalClauseFans decider symbols).length := by
  unfold directSourceFinalClauseIncidenceQueries
  simp [Nat.mul_comm]

/-- The compiled generic stream contains exactly one finite-table direction
block per final clause-core triple and color. -/
theorem directSourceFinalClauseIncidenceDirectionTokens_eq_blocks
    (symbols : List encoding.Γ) :
    directSourceFinalClauseIncidenceDirectionTokens decider symbols =
      FiniteAlphabetDelimitedBlockJoin.blocks
        ((directSourceFinalClauseIncidenceQueries decider symbols).map
          HorizontalFiniteIncidenceDirectionQuery.directions) := by
  unfold directSourceFinalClauseIncidenceDirectionTokens
    directSourceFinalClauseIncidenceNormalizedDirectionTokens
    HorizontalFiniteIncidenceDirectionQuery.delimitedOutput
  exact variableIncidenceConvertedQueryBlocks
    (directSourceFinalClauseIncidenceQueries decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction
