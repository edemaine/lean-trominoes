/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Constant unary fields aligned with an existing field stream -/

noncomputable section

namespace LeanTrominoes
namespace UnaryFieldConstantStreams

open Computability Turing

abbrev Symbol := UnaryFieldEncoderMachine.Symbol

/-- Replace every unary field by zero, preserving the number of fields. -/
def zeros (values : List Nat) : List Nat := values.map fun _ => 0

/-- Replace every unary field by one, preserving the number of fields. -/
def ones (values : List Nat) : List Nat := values.map fun _ => 1

def zeroBlock : Symbol → List Symbol
  | .unit => []
  | .delimiter => [.delimiter]

def oneBlock : Symbol → List Symbol
  | .unit => []
  | .delimiter => [.unit, .delimiter]

theorem flatMap_zeroBlock_unaryField (value : Nat) :
    (UnaryFieldEncoderMachine.unaryField value).flatMap zeroBlock =
      UnaryFieldEncoderMachine.unaryField 0 := by
  simp [UnaryFieldEncoderMachine.unaryField, zeroBlock]

theorem flatMap_oneBlock_unaryField (value : Nat) :
    (UnaryFieldEncoderMachine.unaryField value).flatMap oneBlock =
      UnaryFieldEncoderMachine.unaryField 1 := by
  simp [UnaryFieldEncoderMachine.unaryField, oneBlock]

theorem flatMap_zeroBlock_unaryFields (values : List Nat) :
    (UnaryFieldEncoderMachine.unaryFields values).flatMap zeroBlock =
      UnaryFieldEncoderMachine.unaryFields (zeros values) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons, List.flatMap_append,
        flatMap_zeroBlock_unaryField, induction]
      rfl

theorem flatMap_oneBlock_unaryFields (values : List Nat) :
    (UnaryFieldEncoderMachine.unaryFields values).flatMap oneBlock =
      UnaryFieldEncoderMachine.unaryFields (ones values) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons, List.flatMap_append,
        flatMap_oneBlock_unaryField, induction]
      rfl

/-- A zero field for every input field is computable in linear time. -/
noncomputable def zerosComputableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields zeros := by
  let compiler := FiniteBlockTransducer.computableInPolyTime zeroBlock
  let physical : TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id
      (fun values =>
        (UnaryFieldEncoderMachine.unaryFields values).flatMap zeroBlock) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      UnaryFieldEncoderMachine.unaryFields compiler
      (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    (flatMap_zeroBlock_unaryFields)

/-- A one field for every input field is computable in linear time. -/
noncomputable def onesComputableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields ones := by
  let compiler := FiniteBlockTransducer.computableInPolyTime oneBlock
  let physical : TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id
      (fun values =>
        (UnaryFieldEncoderMachine.unaryFields values).flatMap oneBlock) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      UnaryFieldEncoderMachine.unaryFields compiler
      (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    (flatMap_oneBlock_unaryFields)

end UnaryFieldConstantStreams
end LeanTrominoes

end
