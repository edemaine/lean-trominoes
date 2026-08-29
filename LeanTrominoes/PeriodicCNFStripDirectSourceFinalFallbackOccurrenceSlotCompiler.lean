/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceMaskCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceMaskLength
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGlobalTerminalSlotCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Compiling fallback-family occurrence slots -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFallbackOccurrenceSlotCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

private noncomputable def
    directSourceFinalSelectedFallbackOccurrenceSlotsComputableInPolyTime
    (carrierActive bendActive : Bool) :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List RetainedTerminalSlot)
      encoding.Γ RetainedTerminalSlot id id
      (fun symbols =>
        AlignedRetainedTerminalSlotFilter.selected
          (directSourceFinalFallbackOccurrenceMask decider
            carrierActive bendActive symbols)
          (directSourceFinalGlobalTerminalSlots decider symbols)) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    exact
      AlignedRetainedTerminalSlotFilter.selectedComputableInPolyTimeOf
        id
        (directSourceFinalFallbackOccurrenceMask decider
          carrierActive bendActive)
        (directSourceFinalGlobalTerminalSlots decider)
        (fun symbols => by
          rw [directSourceFinalFallbackOccurrenceMask_length]
          have aligned :=
            (directSourceFinalOccurrenceMasks_length_eq_slots
              decider symbols).1
          rw [directSourceFinalCarrierOccurrenceMask_length] at aligned
          exact aligned)
        (directSourceFinalFallbackOccurrenceMaskComputableInPolyTime
          decider carrierActive bendActive)
        (by
          change @TM2ComputableInPolyTime
            (List encoding.Γ) (List RetainedTerminalSlot)
            encoding.Γ RetainedTerminalSlot id id
            (directSourceFinalGlobalTerminalSlots decider)
          exact directSourceFinalGlobalTerminalSlotsComputableInPolyTime
            decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

/-- Select the presentation-ordered terminal slots of all carrier fallback
occurrences. -/
noncomputable def
    directSourceFinalCarrierOccurrenceSlotsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List RetainedTerminalSlot)
      encoding.Γ RetainedTerminalSlot id id
      (directSourceFinalCarrierOccurrenceSlots decider) := by
  unfold directSourceFinalCarrierOccurrenceSlots
    directSourceFinalCarrierOccurrenceMask
  exact directSourceFinalSelectedFallbackOccurrenceSlotsComputableInPolyTime
    decider true false

/-- Select the presentation-ordered terminal slots of all bend fallback
occurrences. -/
noncomputable def
    directSourceFinalBendOccurrenceSlotsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List RetainedTerminalSlot)
      encoding.Γ RetainedTerminalSlot id id
      (directSourceFinalBendOccurrenceSlots decider) := by
  unfold directSourceFinalBendOccurrenceSlots
    directSourceFinalBendOccurrenceMask
  exact directSourceFinalSelectedFallbackOccurrenceSlotsComputableInPolyTime
    decider false true

end LeanTrominoes.PeriodicCNFStripReduction

end
