/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierQuerySlotBlockArity

/-! # Arity alignment of the final bend family -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendArityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendArityVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalBendQueryArity_eq_slotBlockLengths
    (symbols : List encoding.Γ) :
    (directRetainedFinalBendClauseQueries decider symbols).map
        FinalOccurrenceRoleSlotGrouper.queryArity =
      (directSourceFinalBendStableRankSlotBlocks decider symbols).map
        List.length := by
  have tail := directSourceFinalFallbackArityTail_eq decider symbols
  have carrierLength :
      ((directRetainedFinalCarrierClauseQueries decider symbols).map
          FinalOccurrenceRoleSlotGrouper.queryArity).length =
        ((directSourceFinalCarrierStableRankSlotBlocks
            decider symbols).map List.length).length := by
    simpa only [List.length_map] using
      directSourceFinalCarrierQuerySlotBlocks_length decider symbols
  have bendLength :
      ((directRetainedFinalBendClauseQueries decider symbols).map
          FinalOccurrenceRoleSlotGrouper.queryArity).length =
        ((directSourceFinalBendStableRankSlotBlocks
            decider symbols).map List.length).length := by
    simpa only [List.length_map] using
      directSourceFinalBendQuerySlotBlocks_length decider symbols
  let carrierPrefixLength :=
    ((directRetainedFinalCarrierClauseQueries decider symbols).map
      FinalOccurrenceRoleSlotGrouper.queryArity).length
  let bendPrefixLength :=
    ((directRetainedFinalBendClauseQueries decider symbols).map
      FinalOccurrenceRoleSlotGrouper.queryArity).length
  have selected := congrArg
    (fun values =>
      (values.drop carrierPrefixLength).take bendPrefixLength) tail
  calc
    (directRetainedFinalBendClauseQueries decider symbols).map
          FinalOccurrenceRoleSlotGrouper.queryArity =
        ((directSourceFinalFallbackQueryArityTail
            decider symbols).drop carrierPrefixLength).take
          bendPrefixLength := by
      unfold directSourceFinalFallbackQueryArityTail
        carrierPrefixLength bendPrefixLength
      rw [List.append_assoc]
      rw [List.drop_append_of_le_length (Nat.le_refl _),
        List.drop_length, List.nil_append]
      rw [List.take_append_of_le_length (Nat.le_refl _),
        List.take_length]
    _ = ((directSourceFinalFallbackSlotBlockLengthTail
            decider symbols).drop carrierPrefixLength).take
          bendPrefixLength := selected
    _ = (directSourceFinalBendStableRankSlotBlocks
          decider symbols).map List.length := by
      unfold directSourceFinalFallbackSlotBlockLengthTail
        carrierPrefixLength bendPrefixLength
      rw [carrierLength]
      rw [List.append_assoc]
      rw [List.drop_append_of_le_length (Nat.le_refl _),
        List.drop_length, List.nil_append]
      rw [bendLength]
      rw [List.take_append_of_le_length (Nat.le_refl _),
        List.take_length]

end LeanTrominoes.PeriodicCNFStripReduction

end
