/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryAlignedAddTime
import LeanTrominoes.UnaryAlignedAddValidity

/-! # Polynomial-time pointwise addition of aligned unary lists -/

noncomputable section

namespace LeanTrominoes.AlignedUnaryListClosure

open Computability Turing

def additionInput (first second : List Nat)
    (lengthEq : first.length = second.length) :
    UnaryAlignedAddMachine.Input where
  firsts := first
  seconds := second
  valid := UnaryAlignedAddMachine.Valid.of_length_eq lengthEq

def added (first second : List Nat) : List Nat :=
  UnaryAlignedAddMachine.sums first second

@[simp] theorem added_length (first second : List Nat) :
    (added first second).length = min first.length second.length := by
  unfold added
  induction first generalizing second with
  | nil => simp [UnaryAlignedAddMachine.sums]
  | cons first firsts induction =>
      cases second with
      | nil => simp [UnaryAlignedAddMachine.sums]
      | cons second seconds =>
          simp [UnaryAlignedAddMachine.sums, induction]

/-- Equal-length unary lists produced from one input can be added pointwise
in polynomial time. -/
noncomputable def addedComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (first second : Input → List Nat)
    (lengthEq : ∀ input,
      (first input).length = (second input).length)
    (firstCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields first)
    (secondCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields second) :
    @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => added (first input) (second input)) := by
  let paired := TM2ForkMachine.computableInPolyTime
    firstCompiler secondCompiler
  let prepared : TM2ComputableInPolyTime encodeInput
      UnaryAlignedAddMachine.encode
      (fun input => additionInput
        (first input) (second input) (lengthEq input)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
      (fun _ => rfl)
  let composed := TM2CompositionMachine.computableInPolyTime prepared
    UnaryAlignedAddMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    composed (fun _ => rfl)

end LeanTrominoes.AlignedUnaryListClosure

end
