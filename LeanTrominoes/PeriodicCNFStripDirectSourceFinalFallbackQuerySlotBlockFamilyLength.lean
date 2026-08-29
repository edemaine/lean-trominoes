/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverQueryFamilyLength
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedClauseQueryFamilyLength
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedVariableQueryFamilyLength
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockArity
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockFamilySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockFamilyLength

/-! # Length alignment of the combined final fallback families -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFallbackQuerySlotLengthStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalFallbackQuerySlotLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Carrier and bend queries form one adjacent fallback block. Its length
matches the corresponding two slot-block families without separately
normalizing either metadata representation. -/
theorem directSourceFinalFallbackQuerySlotBlocks_length
    (symbols : List encoding.Γ) :
    (directRetainedFinalCarrierClauseQueries decider symbols ++
      directRetainedFinalBendClauseQueries decider symbols).length =
      (directSourceFinalCarrierStableRankSlotBlocks decider symbols ++
        directSourceFinalBendStableRankSlotBlocks
          decider symbols).length := by
  have total :=
    directSourceFinalQuery_length_eq_stableRankSlotBlocks decider symbols
  rw [directSourceFinalStableRankSlotBlocks_eq_fiveFamilies] at total
  unfold directRetainedFinalClauseQueryAssembly
    directRetainedFinalCarrierClauseQuerySuffix
    directRetainedFinalBendClauseQuerySuffix
    directRetainedFinalRoutedClauseQuerySuffix at total
  have crossoverQuery :=
    directRetainedFinalCrossoverClauseQueries_length decider symbols
  have crossoverBlocks :=
    directSourceFinalCrossoverStableRankSlotBlocks_length decider symbols
  have routedClauseQuery :=
    directRetainedFinalRoutedClauseQueries_length decider symbols
  have routedClauseBlocks :=
    directSourceFinalRoutedClauseStableRankSlotBlocks_length decider symbols
  have routedVariableQuery :=
    directRetainedFinalRoutedVariableClauseQueries_length decider symbols
  have routedVariableBlocks :=
    directSourceFinalRoutedVariableStableRankSlotBlocks_length decider symbols
  simp only [List.length_append] at total ⊢
  omega

end LeanTrominoes.PeriodicCNFStripReduction

end
