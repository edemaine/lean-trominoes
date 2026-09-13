/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryFieldRangeCompiler
import LeanTrominoes.UnaryFieldUnitLengthBroadcastCompiler
import LeanTrominoes.FiniteUnaryFieldBlockMapCompiler

/-! # Unary sums, field counts, and ranges bounded by unary values -/

noncomputable section
namespace LeanTrominoes.UnaryFieldAggregate
open Computability Turing
open UnaryFieldEncoderMachine (Symbol unaryField unaryFields)

def expandBlock : Symbol → List Nat
  | .unit => [0]
  | .delimiter => []

theorem expand_field (n : Nat) :
    (unaryField n).flatMap expandBlock = List.replicate n 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [unaryField,List.replicate_succ,expandBlock] using congrArg (0 :: ·) ih

theorem expand_fields (values : List Nat) :
    (unaryFields values).flatMap expandBlock = List.replicate values.sum 0 := by
  induction values with
  | nil => rfl
  | cons n values ih =>
    rw [UnaryFieldEncoderMachine.unaryFields_cons,List.flatMap_append,expand_field,ih,List.sum_cons,List.replicate_add]

def zerosOfSumCompiler : TM2ComputableInPolyTime unaryFields unaryFields
    (fun values => List.replicate values.sum 0) := by
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    (FiniteUnaryFieldBlockMap.computableInPolyTime expandBlock) (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq raw
    (fun values => congrArg unaryFields (expand_fields values))

def rangeSumCompiler : TM2ComputableInPolyTime unaryFields unaryFields
    (fun values => List.range values.sum) := by
  let compiler := TM2CompositionMachine.computableInPolyTime zerosOfSumCompiler UnaryFieldRange.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiler
    (fun values => congrArg unaryFields (by simp [UnaryFieldRange.values]))

def countBlock : Symbol → List Unit
  | .unit => []
  | .delimiter => [()]

theorem count_field (n : Nat) : (unaryField n).flatMap countBlock = [()] := by
  simp [unaryField,countBlock]

theorem count_fields (values : List Nat) :
    (unaryFields values).flatMap countBlock = List.replicate values.length () := by
  induction values with
  | nil => rfl
  | cons n values ih =>
    rw [UnaryFieldEncoderMachine.unaryFields_cons,List.flatMap_append,count_field,ih]
    rfl

def countCompiler : TM2ComputableInPolyTime unaryFields unaryFields (fun values => [values.length]) := by
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    (FiniteBlockTransducer.computableInPolyTime countBlock) (fun _ => rfl) (fun _ => rfl)
  let counted := TM2CompositionMachine.computableInPolyTime raw UnaryFieldUnitLengthBroadcast.singletonComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq counted
    (fun values => congrArg unaryFields (by rw [count_fields,List.length_replicate]))

def sumCompiler : TM2ComputableInPolyTime unaryFields unaryFields (fun values => [values.sum]) := by
  let compiler := TM2CompositionMachine.computableInPolyTime zerosOfSumCompiler countCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiler
    (fun values => congrArg unaryFields (by simp))

end LeanTrominoes.UnaryFieldAggregate
