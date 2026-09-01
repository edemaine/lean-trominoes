/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Constant Boolean streams aligned with unary fields -/

noncomputable section

namespace LeanTrominoes.UnaryFieldConstantBits

open Computability Turing

abbrev Symbol := UnaryFieldEncoderMachine.Symbol

def values (bit : Bool) (source : List Nat) : List Bool :=
  source.map fun _ => bit

def block (bit : Bool) : Symbol → List Bool
  | .unit => []
  | .delimiter => [bit]

theorem flatMap_block_unaryField (bit : Bool) (value : Nat) :
    (UnaryFieldEncoderMachine.unaryField value).flatMap (block bit) =
      [bit] := by
  simp [UnaryFieldEncoderMachine.unaryField, block]

theorem flatMap_block_unaryFields (bit : Bool) (source : List Nat) :
    (UnaryFieldEncoderMachine.unaryFields source).flatMap (block bit) =
      values bit source := by
  induction source with
  | nil => rfl
  | cons value source induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        List.flatMap_append, flatMap_block_unaryField, induction]
      rfl

/-- Replacing every unary field by one fixed Boolean is a finite block
transduction. -/
noncomputable def computableInPolyTime (bit : Bool) :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id (values bit) := by
  let physical : TM2ComputableInPolyTime id id
      (fun source : List Symbol => source.flatMap (block bit)) :=
    FiniteBlockTransducer.computableInPolyTime (block bit)
  let prepared : TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id
      (fun source =>
        (UnaryFieldEncoderMachine.unaryFields source).flatMap (block bit)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      UnaryFieldEncoderMachine.unaryFields physical
      (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    prepared (flatMap_block_unaryFields bit)

end LeanTrominoes.UnaryFieldConstantBits

end
