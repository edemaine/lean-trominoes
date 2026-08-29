/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackQuerySlotBlockArityTail

/-! # Arity alignment of the final carrier family -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierArityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierArityVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalCarrierQueryArity_eq_slotBlockLengths
    (symbols : List encoding.Γ) :
    (directRetainedFinalCarrierClauseQueries decider symbols).map
        FinalOccurrenceRoleSlotGrouper.queryArity =
      (directSourceFinalCarrierStableRankSlotBlocks decider symbols).map
        List.length := by
  have tail := directSourceFinalFallbackArityTail_eq decider symbols
  have carrierLength :
      ((directRetainedFinalCarrierClauseQueries decider symbols).map
          FinalOccurrenceRoleSlotGrouper.queryArity).length =
        ((directSourceFinalCarrierStableRankSlotBlocks
            decider symbols).map List.length).length := by
    simpa only [List.length_map] using
      directSourceFinalCarrierQuerySlotBlocks_length decider symbols
  let prefixLength :=
    ((directRetainedFinalCarrierClauseQueries decider symbols).map
      FinalOccurrenceRoleSlotGrouper.queryArity).length
  have taken := congrArg (List.take prefixLength) tail
  calc
    (directRetainedFinalCarrierClauseQueries decider symbols).map
          FinalOccurrenceRoleSlotGrouper.queryArity =
        (directSourceFinalFallbackQueryArityTail
          decider symbols).take prefixLength := by
      unfold directSourceFinalFallbackQueryArityTail prefixLength
      rw [List.append_assoc]
      rw [List.take_append_of_le_length (Nat.le_refl _),
        List.take_length]
    _ = (directSourceFinalFallbackSlotBlockLengthTail
          decider symbols).take prefixLength := taken
    _ = (directSourceFinalCarrierStableRankSlotBlocks
          decider symbols).map List.length := by
      unfold directSourceFinalFallbackSlotBlockLengthTail prefixLength
      rw [carrierLength]
      rw [List.append_assoc]
      rw [List.take_append_of_le_length (Nat.le_refl _),
        List.take_length]

end LeanTrominoes.PeriodicCNFStripReduction

end
