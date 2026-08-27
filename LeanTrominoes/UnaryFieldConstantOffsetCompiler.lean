/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Adding a fixed offset to every unary field -/

noncomputable section

namespace LeanTrominoes.UnaryFieldConstantOffsets

open Computability Turing

abbrev Symbol := UnaryFieldEncoderMachine.Symbol

def values (offset : Nat) (source : List Nat) : List Nat :=
  source.map fun value => value + offset

def block (offset : Nat) : Symbol → List Symbol
  | .unit => [.unit]
  | .delimiter => List.replicate offset .unit ++ [.delimiter]

theorem flatMap_block_unaryField (offset value : Nat) :
    (UnaryFieldEncoderMachine.unaryField value).flatMap (block offset) =
      UnaryFieldEncoderMachine.unaryField (value + offset) := by
  have units :
      (List.replicate value UnaryFieldEncoderMachine.Symbol.unit).flatMap
          (block offset) =
        List.replicate value UnaryFieldEncoderMachine.Symbol.unit := by
    induction value with
    | zero => rfl
    | succ value induction =>
        simp [List.replicate_succ, List.flatMap_cons, block, induction]
  unfold UnaryFieldEncoderMachine.unaryField
  rw [List.flatMap_append, units]
  simp only [List.flatMap_cons, List.flatMap_nil, block,
    List.append_nil]
  rw [← List.append_assoc, ← List.replicate_add]

theorem flatMap_block_unaryFields (offset : Nat) (source : List Nat) :
    (UnaryFieldEncoderMachine.unaryFields source).flatMap (block offset) =
      UnaryFieldEncoderMachine.unaryFields (values offset source) := by
  induction source with
  | nil => rfl
  | cons value source induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons, List.flatMap_append,
        flatMap_block_unaryField, induction]
      rfl

/-- Adding any fixed constant to every field is computable in linear time. -/
noncomputable def computableInPolyTime (offset : Nat) :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields (values offset) := by
  let compiler := FiniteBlockTransducer.computableInPolyTime (block offset)
  let physical : TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id
      (fun source =>
        (UnaryFieldEncoderMachine.unaryFields source).flatMap
          (block offset)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      UnaryFieldEncoderMachine.unaryFields compiler
      (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    (flatMap_block_unaryFields offset)

end LeanTrominoes.UnaryFieldConstantOffsets

end
