/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackDescriptorSlotBlockArity
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceMaskLength
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockFamilySemantics

/-! # Four-block semantics of final fallback occurrence masks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFallbackMaskFamilyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalFallbackMaskFamilyVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

def directSourceFinalCrossoverStableRankSlots
    (symbols : List encoding.Γ) : List RetainedTerminalSlot :=
  (directSourceFinalCrossoverStableRankSlotBlocks
    decider symbols).flatten

def directSourceFinalCarrierStableRankSlots
    (symbols : List encoding.Γ) : List RetainedTerminalSlot :=
  (directSourceFinalCarrierStableRankSlotBlocks
    decider symbols).flatten

def directSourceFinalBendStableRankSlots
    (symbols : List encoding.Γ) : List RetainedTerminalSlot :=
  (directSourceFinalBendStableRankSlotBlocks
    decider symbols).flatten

def directSourceFinalRoutedStableRankSlots
    (symbols : List encoding.Γ) : List RetainedTerminalSlot :=
  (directSourceFinalRoutedClauseStableRankSlotBlocks decider symbols ++
    directSourceFinalRoutedVariableStableRankSlotBlocks
      decider symbols).flatten

theorem directSourceFinalGlobalTerminalSlots_eq_fourFamilies
    (symbols : List encoding.Γ) :
    directSourceFinalGlobalTerminalSlots decider symbols =
      directSourceFinalCrossoverStableRankSlots decider symbols ++
        (directSourceFinalCarrierStableRankSlots decider symbols ++
          (directSourceFinalBendStableRankSlots decider symbols ++
            directSourceFinalRoutedStableRankSlots decider symbols)) := by
  unfold directSourceFinalGlobalTerminalSlots
  rw [← directSourceFinalStableRankSlotBlocks_flatten]
  rw [directSourceFinalStableRankSlotBlocks_eq_fiveFamilies]
  unfold directSourceFinalCrossoverStableRankSlots
    directSourceFinalCarrierStableRankSlots
    directSourceFinalBendStableRankSlots
    directSourceFinalRoutedStableRankSlots
  simp only [List.flatten_append, List.append_assoc]

theorem directSourceFinalRoutedOccurrenceMaskSuffix_eq_replicate_length
    (symbols : List encoding.Γ) :
    directSourceFinalRoutedOccurrenceMaskSuffix decider symbols =
      List.replicate
        (directSourceFinalRoutedOccurrenceMaskSuffix
          decider symbols).length false := by
  unfold directSourceFinalRoutedOccurrenceMaskSuffix
  simp only [descriptorOccurrenceMask_eq_replicate,
    List.length_append, List.length_replicate]
  rw [← List.replicate_add]

theorem directSourceFinalFallbackOccurrenceMask_eq_familyReplicates
    (carrierActive bendActive : Bool)
    (symbols : List encoding.Γ) :
    directSourceFinalFallbackOccurrenceMask decider
        carrierActive bendActive symbols =
      List.replicate
          (directSourceFinalCrossoverStableRankSlots
            decider symbols).length false ++
        (List.replicate
            (directSourceFinalCarrierStableRankSlots
              decider symbols).length carrierActive ++
          (List.replicate
              (directSourceFinalBendStableRankSlots
                decider symbols).length bendActive ++
            List.replicate
              (directSourceFinalRoutedOccurrenceMaskSuffix
                decider symbols).length false)) := by
  unfold directSourceFinalFallbackOccurrenceMask
    directSourceFinalCarrierOccurrenceMaskSuffix
    directSourceFinalBendOccurrenceMaskSuffix
    directSourceFinalCrossoverStableRankSlots
    directSourceFinalCarrierStableRankSlots
    directSourceFinalBendStableRankSlots
  rw [directSourceFinalCrossoverOccurrenceMaskBlock_eq_replicate,
    directSourceFinalCarrierOccurrenceMaskBlock_eq_replicate,
    directSourceFinalBendOccurrenceMaskBlock_eq_replicate]
  exact congrArg
    (fun routed =>
      List.replicate
            (directSourceFinalCrossoverStableRankSlotBlocks
              decider symbols).flatten.length false ++
        (List.replicate
            (directSourceFinalCarrierStableRankSlotBlocks
              decider symbols).flatten.length carrierActive ++
          (List.replicate
              (directSourceFinalBendStableRankSlotBlocks
                decider symbols).flatten.length bendActive ++ routed)))
    (directSourceFinalRoutedOccurrenceMaskSuffix_eq_replicate_length
      decider symbols)

theorem directSourceFinalRoutedOccurrenceMaskSuffix_length_eq_slots
    (symbols : List encoding.Γ) :
    (directSourceFinalRoutedOccurrenceMaskSuffix decider symbols).length =
      (directSourceFinalRoutedStableRankSlots decider symbols).length := by
  have full :=
    (directSourceFinalOccurrenceMasks_length_eq_slots decider symbols).1
  unfold directSourceFinalCarrierOccurrenceMask at full
  rw [directSourceFinalFallbackOccurrenceMask_eq_familyReplicates]
    at full
  rw [directSourceFinalGlobalTerminalSlots_eq_fourFamilies] at full
  simp only [List.length_append, List.length_replicate] at full
  omega

theorem directSourceFinalFallbackOccurrenceMask_eq_slotReplicates
    (carrierActive bendActive : Bool)
    (symbols : List encoding.Γ) :
    directSourceFinalFallbackOccurrenceMask decider
        carrierActive bendActive symbols =
      List.replicate
          (directSourceFinalCrossoverStableRankSlots
            decider symbols).length false ++
        (List.replicate
            (directSourceFinalCarrierStableRankSlots
              decider symbols).length carrierActive ++
          (List.replicate
              (directSourceFinalBendStableRankSlots
                decider symbols).length bendActive ++
            List.replicate
              (directSourceFinalRoutedStableRankSlots
                decider symbols).length false)) := by
  rw [directSourceFinalFallbackOccurrenceMask_eq_familyReplicates,
    directSourceFinalRoutedOccurrenceMaskSuffix_length_eq_slots]

end LeanTrominoes.PeriodicCNFStripReduction

end
