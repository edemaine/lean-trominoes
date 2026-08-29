/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockFamilyData

/-! # Lengths of the five stable-rank slot-block families -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalSlotBlockFamilyLengthStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalSlotBlockFamilyLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalCrossoverStableRankSlotBlocks_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCrossoverStableRankSlotBlocks
      decider symbols).length =
      (directSourceFinalCrossoverClauses decider symbols).length := by
  unfold directSourceFinalCrossoverStableRankSlotBlocks
  exact directSourceFinalStableRankSlotBlocksFrom_length _ _ _ _

theorem directSourceFinalCarrierStableRankSlotBlocks_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierStableRankSlotBlocks decider symbols).length =
      (directSourceFinalCarrierClauses decider symbols).length := by
  unfold directSourceFinalCarrierStableRankSlotBlocks
  exact directSourceFinalStableRankSlotBlocksFrom_length _ _ _ _

theorem directSourceFinalBendStableRankSlotBlocks_length
    (symbols : List encoding.Γ) :
    (directSourceFinalBendStableRankSlotBlocks decider symbols).length =
      (directSourceFinalBendClauses decider symbols).length := by
  unfold directSourceFinalBendStableRankSlotBlocks
  exact directSourceFinalStableRankSlotBlocksFrom_length _ _ _ _

theorem directSourceFinalRoutedClauseStableRankSlotBlocks_length
    (symbols : List encoding.Γ) :
    (directSourceFinalRoutedClauseStableRankSlotBlocks
      decider symbols).length =
      (directSourceFinalRoutedClauseClauses decider symbols).length := by
  unfold directSourceFinalRoutedClauseStableRankSlotBlocks
  exact directSourceFinalStableRankSlotBlocksFrom_length _ _ _ _

theorem directSourceFinalRoutedVariableStableRankSlotBlocks_length
    (symbols : List encoding.Γ) :
    (directSourceFinalRoutedVariableStableRankSlotBlocks
      decider symbols).length =
      (directSourceFinalRoutedVariableClauses decider symbols).length := by
  unfold directSourceFinalRoutedVariableStableRankSlotBlocks
  exact directSourceFinalStableRankSlotBlocksFrom_length _ _ _ _

end LeanTrominoes.PeriodicCNFStripReduction

end
