/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleInheritedRingAtomCodeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedInheritedRingAtomCodeSemantics
import LeanTrominoes.UnaryFieldEncoderAppendClosure

/-! # Complete direct final inherited ring-atom codes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalInheritedRingCodeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Complete inherited base-nine code column in canonical copied-plus-cycle
occurrence order. -/
def directSourceFinalInheritedRingAtomCodes
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalCopiedInheritedRingAtomCodes decider symbols ++
    directSourceFinalCycleInheritedRingAtomCodes decider symbols

@[simp] theorem directSourceFinalInheritedRingAtomCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalInheritedRingAtomCodes decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalInheritedRingAtomCodes, List.length_append,
    directSourceFinalCopiedInheritedRingAtomCodes_length,
    directSourceFinalCycleInheritedRingAtomCodes_length,
    directSourceFinalCompiledOccurrenceData_eq_copied_cycle,
    List.length_append]

/-- The complete inherited ring-code column is polynomial-time computable,
including for the formally possible empty source alphabet. -/
noncomputable def
    directSourceFinalInheritedRingAtomCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalInheritedRingAtomCodes decider) := by
  unfold directSourceFinalInheritedRingAtomCodes
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceFinalCopiedInheritedRingAtomCodesComputableInPolyTime
      decider)
    (directSourceFinalCycleInheritedRingAtomCodesComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
