/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalClauseDescriptorAssemblySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceMaskData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotLength

/-! # Length alignment of fallback-family occurrence masks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFallbackOccurrenceMaskLengthStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

theorem directSourceFinalFallbackOccurrenceMask_length
    (carrierActive bendActive : Bool)
    (symbols : List encoding.Γ) :
    (directSourceFinalFallbackOccurrenceMask decider
      carrierActive bendActive symbols).length =
      (retainedFinalCopiedClauseOccurrenceRoles
        (directRetainedFinalClauseQueryAssembly decider symbols)).length := by
  unfold directSourceFinalFallbackOccurrenceMask
    directSourceFinalCarrierOccurrenceMaskSuffix
    directSourceFinalBendOccurrenceMaskSuffix
    directSourceFinalRoutedOccurrenceMaskSuffix
  simp only [List.length_append, descriptorOccurrenceMask_length]
  rw [retainedFinalCopiedClauseOccurrenceRoles_length]
  have familyEq := congrArg
    (fun descriptors =>
      (descriptors.map retainedFinalCopiedDescriptorArity).sum)
    (directRetainedFinalClauseDescriptorAssembly_eq_families
      decider symbols)
  unfold directRetainedFinalClauseDescriptorAssembly at familyEq
  simp only [List.map_append, List.sum_append] at familyEq
  simpa only [Nat.add_assoc] using familyEq.symm

theorem directSourceFinalBendOccurrenceMask_length
    (symbols : List encoding.Γ) :
    (directSourceFinalBendOccurrenceMask decider symbols).length =
      (retainedFinalCopiedClauseOccurrenceRoles
        (directRetainedFinalClauseQueryAssembly decider symbols)).length := by
  exact directSourceFinalFallbackOccurrenceMask_length
    decider false true symbols

theorem directSourceFinalCarrierOccurrenceMask_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierOccurrenceMask decider symbols).length =
      (retainedFinalCopiedClauseOccurrenceRoles
        (directRetainedFinalClauseQueryAssembly decider symbols)).length := by
  exact directSourceFinalFallbackOccurrenceMask_length
    decider true false symbols

theorem directSourceFinalOccurrenceMasks_length_eq_slots
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierOccurrenceMask decider symbols).length =
        (directSourceFinalGlobalTerminalSlots decider symbols).length ∧
      (directSourceFinalBendOccurrenceMask decider symbols).length =
        (directSourceFinalGlobalTerminalSlots decider symbols).length := by
  have aligned :=
    directSourceFinalOccurrenceRoleBaseValues_length_eq_slots
      decider symbols
  unfold directSourceFinalOccurrenceRoleBaseValues
    directSourceFinalTerminalSlotValues FiniteUnaryFieldMap.values at aligned
  simp only [List.length_map] at aligned
  rw [directSourceFinalCarrierOccurrenceMask_length,
    directSourceFinalBendOccurrenceMask_length]
  exact ⟨aligned, aligned⟩

end LeanTrominoes.PeriodicCNFStripReduction

end
