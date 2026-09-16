/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnCompiler

/-! # Expanding a unary bound into its list of smaller naturals -/
noncomputable section
namespace LeanTrominoes.UnaryNaturalRange
open Computability Turing
open UnaryFieldEncoderMachine (Symbol unaryField unaryFields)

def block : Symbol → List Symbol
  | .unit => [.delimiter]
  | .delimiter => []

theorem field_zeroes (n : Nat) :
    (unaryFields [n]).flatMap block = unaryFields (List.replicate n 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [unaryFields,unaryField,List.replicate_succ,block] using congrArg (List.cons Symbol.delimiter) ih

def computableInPolyTime : TM2ComputableInPolyTime (fun n => unaryFields [n]) unaryFields List.range := by
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare (fun n => unaryFields [n])
    (FiniteBlockTransducer.computableInPolyTime block) (fun _ => rfl) (fun _ => rfl)
  let zeros : TM2ComputableInPolyTime (fun n => unaryFields [n]) unaryFields (fun n => List.replicate n 0) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq raw field_zeroes
  let result := TM2CompositionMachine.computableInPolyTime zeros UnaryFieldRange.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun n => congrArg unaryFields (by simp [UnaryFieldRange.values]))
end LeanTrominoes.UnaryNaturalRange
