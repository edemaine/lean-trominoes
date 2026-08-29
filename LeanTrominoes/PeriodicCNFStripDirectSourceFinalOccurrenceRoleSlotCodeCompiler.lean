/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotLength
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Compiler for aligned final occurrence-role and slot codes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoleSlotCodeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Each occurrence code is its finite query-role block base plus the
corresponding bounded terminal-slot value. -/
def directSourceFinalOccurrenceRoleSlotCodes
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalOccurrenceRoleBaseValues decider symbols)
    (directSourceFinalTerminalSlotValues decider symbols)

/-- Pointwise unary addition compiles the complete aligned role/slot code
stream, including the formally possible empty source alphabet. -/
noncomputable def
    directSourceFinalOccurrenceRoleSlotCodesComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Nat)
      encoding.Γ UnaryFieldEncoderMachine.Symbol
      id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOccurrenceRoleSlotCodes decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalOccurrenceRoleSlotCodes
    exact AlignedUnaryListClosure.addedComputableInPolyTime
      id
      (directSourceFinalOccurrenceRoleBaseValues decider)
      (directSourceFinalTerminalSlotValues decider)
      (directSourceFinalOccurrenceRoleBaseValues_length_eq_slots decider)
      (directSourceFinalOccurrenceRoleBaseValuesComputableInPolyTime decider)
      (directSourceFinalTerminalSlotValuesComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end
