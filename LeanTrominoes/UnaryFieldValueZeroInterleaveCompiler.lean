/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Interleaving unary values with zero fields -/

noncomputable section

namespace LeanTrominoes.UnaryFieldValueZeroInterleave

open Computability Turing

abbrev Symbol := UnaryFieldEncoderMachine.Symbol

/-- Replace every unary value by the adjacent pair `[value, 0]`. -/
def values (source : List Nat) : List Nat :=
  source.flatMap fun value => [value, 0]

def block : Symbol → List Symbol
  | .unit => [.unit]
  | .delimiter => [.delimiter, .delimiter]

private theorem flatMap_units (count : Nat) :
    (List.replicate count UnaryFieldEncoderMachine.Symbol.unit).flatMap
        block =
      List.replicate count UnaryFieldEncoderMachine.Symbol.unit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, List.flatMap_cons, block, induction]
      rfl

theorem flatMap_unaryField (value : Nat) :
    (UnaryFieldEncoderMachine.unaryField value).flatMap block =
      UnaryFieldEncoderMachine.unaryField value ++
        UnaryFieldEncoderMachine.unaryField 0 := by
  unfold UnaryFieldEncoderMachine.unaryField
  rw [List.flatMap_append, flatMap_units]
  simp [block]

theorem flatMap_unaryFields (source : List Nat) :
    (UnaryFieldEncoderMachine.unaryFields source).flatMap block =
      UnaryFieldEncoderMachine.unaryFields (values source) := by
  induction source with
  | nil => rfl
  | cons value source induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        List.flatMap_append, flatMap_unaryField, induction]
      change UnaryFieldEncoderMachine.unaryField value ++
          UnaryFieldEncoderMachine.unaryField 0 ++
            UnaryFieldEncoderMachine.unaryFields (values source) =
        UnaryFieldEncoderMachine.unaryFields
          ([value, 0] ++ values source)
      rw [UnaryFieldEncoderMachine.unaryFields_append]
      rfl

@[simp] theorem values_length (source : List Nat) :
    (values source).length = 2 * source.length := by
  induction source with
  | nil => rfl
  | cons value source induction =>
      simp [values]
      omega

/-- Value/zero interleaving is a fixed block transduction and hence runs in
linear time in the unary encoding. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields values := by
  let compiler := FiniteBlockTransducer.computableInPolyTime block
  let physical : TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id
      (fun source =>
        (UnaryFieldEncoderMachine.unaryFields source).flatMap block) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      UnaryFieldEncoderMachine.unaryFields compiler
      (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    flatMap_unaryFields

end LeanTrominoes.UnaryFieldValueZeroInterleave

end
