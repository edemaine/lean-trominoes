/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Generic unary finite-index/slot decoder -/

noncomputable section

namespace LeanTrominoes.FiniteIndexSlotUnaryDecoder

open Computability Turing

abbrev Slot := Fin 8
abbrev Pair (count : Nat) := Fin count × Slot
abbrev Symbol := UnaryFieldEncoderMachine.Symbol

/-- Row-major packing of two finite indices. -/
def pairIndex {firstCount secondCount : Nat}
    (indices : Fin firstCount × Fin secondCount) :
    Fin (firstCount * secondCount) :=
  finProdFinEquiv indices

/-- Row-major unpacking of a product index. -/
def unpairIndex {firstCount secondCount : Nat}
    (index : Fin (firstCount * secondCount)) :
    Fin firstCount × Fin secondCount :=
  finProdFinEquiv.symm index

@[simp] theorem pairIndex_val {firstCount secondCount : Nat}
    (indices : Fin firstCount × Fin secondCount) :
    (pairIndex indices).val = indices.2.val + secondCount * indices.1.val :=
  rfl

@[simp] theorem unpairIndex_pairIndex {firstCount secondCount : Nat}
    (indices : Fin firstCount × Fin secondCount) :
    unpairIndex (pairIndex indices) = indices :=
  finProdFinEquiv.symm_apply_apply indices

def codeBound (count : Nat) : Nat := 8 * count

theorem codeBound_pos (count : Nat) [NeZero count] :
    0 < codeBound count := by
  unfold codeBound
  have countPos : 0 < count := Nat.pos_of_ne_zero (NeZero.ne count)
  omega

/-- Saturate an arbitrary unary field to an explicit finite index and slot. -/
def boundedCode (count : Nat) [NeZero count] (code : Nat) : Pair count :=
  let bounded := min code (codeBound count - 1)
  let index : Fin count :=
    ⟨bounded / 8, by
      have boundedLt : bounded < codeBound count := by
        have := codeBound_pos count
        dsimp only [bounded]
        omega
      unfold codeBound at boundedLt
      omega⟩
  let slot : Slot := ⟨bounded % 8, Nat.mod_lt _ (by omega)⟩
  (index, slot)

def controlCode {count : Nat} (control : Pair count) : Nat :=
  8 * control.1.val + control.2.val

def zero (count : Nat) [NeZero count] : Pair count :=
  boundedCode count 0

def increment {count : Nat} [NeZero count]
    (control : Pair count) : Pair count :=
  boundedCode count (controlCode control + 1)

def advance {count : Nat} [NeZero count] :
    Pair count → Nat → Pair count
  | control, 0 => control
  | control, steps + 1 => advance (increment control) steps

theorem advance_succ {count : Nat} [NeZero count]
    (control : Pair count) (steps : Nat) :
    advance control (Nat.succ steps) = advance (increment control) steps :=
  rfl

def pairs (count : Nat) [NeZero count]
    (codes : List Nat) : List (Pair count) :=
  codes.map (boundedCode count)

def transition {count : Nat} [NeZero count] :
    Pair count → Symbol → Pair count × List (Pair count)
  | control, .unit => (increment control, [])
  | control, .delimiter => (zero count, [control])

def finish {count : Nat} (_ : Pair count) : List (Pair count) := []

/-- A valid mixed-radix code recovers its explicit finite index and slot. -/
theorem boundedCode_index_slot {count : Nat} [NeZero count]
    (index : Fin count) (slot : Slot) :
    boundedCode count (8 * index.val + slot.val) = (index, slot) := by
  have indexLt := index.isLt
  have slotLt := slot.isLt
  have codeLt : 8 * index.val + slot.val < codeBound count := by
    unfold codeBound
    omega
  unfold boundedCode
  apply Prod.ext
  · apply Fin.ext
    simp only
    omega
  · apply Fin.ext
    simp only
    omega

theorem controlCode_boundedCode (count : Nat) [NeZero count]
    (code : Nat) :
    controlCode (boundedCode count code) =
      min code (codeBound count - 1) := by
  unfold controlCode boundedCode
  dsimp only
  have modLt : min code (codeBound count - 1) % 8 < 8 :=
    Nat.mod_lt _ (by omega)
  omega

private theorem boundedCode_congr {count : Nat} [NeZero count]
    {first second : Nat}
    (equal : min first (codeBound count - 1) =
      min second (codeBound count - 1)) :
    boundedCode count first = boundedCode count second := by
  apply Prod.ext
  · apply Fin.ext
    simp only [boundedCode, Fin.val_mk]
    exact congrArg (fun value => value / 8) equal
  · apply Fin.ext
    simp only [boundedCode, Fin.val_mk]
    exact congrArg (fun value => value % 8) equal

theorem increment_boundedCode (count : Nat) [NeZero count]
    (code : Nat) :
    increment (boundedCode count code) = boundedCode count (code + 1) := by
  unfold increment
  rw [controlCode_boundedCode]
  apply boundedCode_congr
  have := codeBound_pos count
  omega

theorem advance_boundedCode (count : Nat) [NeZero count]
    (code steps : Nat) :
    advance (boundedCode count code) steps =
      boundedCode count (code + steps) := by
  induction steps generalizing code with
  | zero => rfl
  | succ steps induction =>
      rw [show advance (boundedCode count code) (Nat.succ steps) =
          advance (increment (boundedCode count code)) steps by rfl,
        increment_boundedCode, induction]
      congr 1
      omega

theorem scan_unaryField {count : Nat} [NeZero count]
    (control : Pair count) (code : Nat) :
    FiniteStateTransducer.scan transition control
        (UnaryFieldEncoderMachine.unaryField code) =
      (zero count, [advance control code]) := by
  induction code generalizing control with
  | zero => rfl
  | succ code induction =>
      rw [UnaryFieldEncoderMachine.unaryField,
        List.replicate_succ, List.cons_append]
      simp only [FiniteStateTransducer.scan, transition]
      rw [← UnaryFieldEncoderMachine.unaryField]
      simpa only [advance_succ, List.nil_append] using
        induction (increment control)

theorem scan_unaryFields (count : Nat) [NeZero count]
    (codes : List Nat) :
    FiniteStateTransducer.scan transition (zero count)
        (UnaryFieldEncoderMachine.unaryFields codes) =
      (zero count, pairs count codes) := by
  induction codes with
  | nil => rfl
  | cons code codes induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        FiniteStateTransducer.scan_append, scan_unaryField]
      dsimp only
      have advanceZero : advance (zero count) code =
          boundedCode count code := by
        simpa [zero] using advance_boundedCode count 0 code
      rw [advanceZero, induction]
      rfl

theorem output_unaryFields (count : Nat) [NeZero count]
    (codes : List Nat) :
    FiniteStateTransducer.output (zero count) transition finish
        (UnaryFieldEncoderMachine.unaryFields codes) = pairs count codes := by
  simp [FiniteStateTransducer.output, scan_unaryFields, finish]

noncomputable def computableInPolyTime (count : Nat) [NeZero count] :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id (pairs count) :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    UnaryFieldEncoderMachine.unaryFields
    (FiniteStateTransducer.computableInPolyTime
      (zero count) transition finish)
    (fun _ => rfl) (output_unaryFields count)

end LeanTrominoes.FiniteIndexSlotUnaryDecoder

end
