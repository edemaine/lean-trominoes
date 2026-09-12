/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryFieldConstantStreamCompiler
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Emit a fixed unary-field table once for every input field -/

noncomputable section
namespace LeanTrominoes.UnaryFieldConstantTable
open Computability Turing
abbrev Symbol := UnaryFieldEncoderMachine.Symbol

def values (table source : List Nat) : List Nat := source.flatMap fun _ => table

def block (table : List Nat) : Symbol → List Symbol
  | .unit => []
  | .delimiter => UnaryFieldEncoderMachine.unaryFields table

theorem flatMap_block_unaryField (table : List Nat) (value : Nat) :
    (UnaryFieldEncoderMachine.unaryField value).flatMap (block table) =
      UnaryFieldEncoderMachine.unaryFields table := by
  simp [UnaryFieldEncoderMachine.unaryField, block]

theorem flatMap_block_unaryFields (table source : List Nat) :
    (UnaryFieldEncoderMachine.unaryFields source).flatMap (block table) =
      UnaryFieldEncoderMachine.unaryFields (values table source) := by
  induction source with
  | nil => rfl
  | cons value source ih =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons, List.flatMap_append,
        flatMap_block_unaryField, ih]
      simp only [values, List.flatMap_cons, UnaryFieldEncoderMachine.unaryFields_append]

/-- Fixed local coordinate or tag tables require only a finite delimiter transducer. -/
noncomputable def computableInPolyTime (table : List Nat) :
    TM2ComputableInPolyTime UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields (values table) := by
  let physical : TM2ComputableInPolyTime UnaryFieldEncoderMachine.unaryFields id
      (fun source => (UnaryFieldEncoderMachine.unaryFields source).flatMap (block table)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare UnaryFieldEncoderMachine.unaryFields
      (FiniteBlockTransducer.computableInPolyTime (block table)) (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical (flatMap_block_unaryFields table)

@[simp] theorem values_length (table source : List Nat) :
    (values table source).length = source.length * table.length := by
  simp [values]

end LeanTrominoes.UnaryFieldConstantTable
end
