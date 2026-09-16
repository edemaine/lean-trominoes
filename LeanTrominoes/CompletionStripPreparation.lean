/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripRawGeometry
import LeanTrominoes.UnaryFieldEncoderMachine
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2ConstantValueCompiler
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time conversion of the exact unary strip encoding -/

namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Preparation
open Turing Computability
open LeanTrominoes.PeriodicStripTrominoPrefill.Raw

abbrev UnarySymbol := UnaryFieldEncoderMachine.Symbol

def unitBlock (bit : Bool) : List UnarySymbol := if bit then [.unit] else []
def fieldBlock (bit : Bool) : List UnarySymbol := [if bit then .unit else .delimiter]
def units (source : List Bool) : List UnarySymbol := source.flatMap unitBlock

def preparedSymbols (source : List Bool) : List UnarySymbol :=
  List.replicate 3 .unit ++ (units source ++ [.delimiter]) ++ source.flatMap fieldBlock

theorem units_append (a b : List Bool) : units (a++b) = units a++units b := List.flatMap_append

theorem units_field (n : Nat) : units (List.replicate n true ++ [false]) = List.replicate n UnaryFieldEncoderMachine.Symbol.unit := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ,units,unitBlock] using congrArg (UnaryFieldEncoderMachine.Symbol.unit :: ·) ih

theorem units_fields (values : List Nat) : units (CompletionStripEncoding.unaryFields values) = List.replicate values.sum UnaryFieldEncoderMachine.Symbol.unit := by
  induction values with
  | nil => rfl
  | cons n values ih =>
    change units ((List.replicate n true ++ [false]) ++ CompletionStripEncoding.unaryFields values) = _
    rw [units_append,units_field,ih,List.sum_cons,List.replicate_add]

theorem fieldBlock_field (n : Nat) :
    (List.replicate n true ++ [false]).flatMap fieldBlock = UnaryFieldEncoderMachine.unaryField n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [List.replicate_succ,fieldBlock,UnaryFieldEncoderMachine.unaryField] using congrArg (UnaryFieldEncoderMachine.Symbol.unit :: ·) ih

theorem fieldBlock_fields (values : List Nat) :
    (CompletionStripEncoding.unaryFields values).flatMap fieldBlock = UnaryFieldEncoderMachine.unaryFields values := by
  induction values with
  | nil => rfl
  | cons n values ih =>
    change ((List.replicate n true ++ [false]) ++ CompletionStripEncoding.unaryFields values).flatMap fieldBlock = _
    rw [List.flatMap_append,fieldBlock_field,ih]
    rfl

theorem preparedSymbols_correct (input : PeriodicStripTrominoPrefill) :
    preparedSymbols (CompletionStripEncoding.finEncoding.encode input) = UnaryFieldEncoderMachine.unaryFields (fields input) := by
  change preparedSymbols (CompletionStripEncoding.unaryFields (CompletionStripEncoding.fields input)) = _
  rw [preparedSymbols,units_fields,fieldBlock_fields]
  simp [fields,bound,UnaryFieldEncoderMachine.unaryFields,UnaryFieldEncoderMachine.unaryField,List.replicate_add,List.append_assoc]

noncomputable def preparedSymbols_compiler : TM2ComputableInPolyTime id id preparedSymbols := by
  let frontCompiler := TM2ConstantValueCompiler.computableInPolyTime (Input := List Bool) id id (List.replicate 3 UnaryFieldEncoderMachine.Symbol.unit)
  let markers := FiniteBlockTransducer.computableInPolyTime unitBlock
  let delimiter := TM2ConstantValueCompiler.computableInPolyTime (Input := List Bool) id id [UnaryFieldEncoderMachine.Symbol.delimiter]
  let data := FiniteBlockTransducer.computableInPolyTime fieldBlock
  exact TM2ListAppend.computableInPolyTime
    (TM2ListAppend.computableInPolyTime frontCompiler (TM2ListAppend.computableInPolyTime markers delimiter)) data

noncomputable def unaryPreparation_compiler :
    TM2ComputableInPolyTime CompletionStripEncoding.finEncoding.encode UnaryFieldEncoderMachine.unaryFields fields := by
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare CompletionStripEncoding.finEncoding.encode
    preparedSymbols_compiler (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq raw preparedSymbols_correct

/-- The front field is the geometric bound, followed by the original decoded fields. -/
noncomputable def nativePreparation_compiler :
    TM2ComputableInPolyTime CompletionStripEncoding.finEncoding.encode Turing.PartrecToTM2.trList fields := by
  let compiler := TM2CompositionMachine.computableInPolyTime unaryPreparation_compiler UnaryFieldEncoderMachine.computableInPolyTime
  exact compiler

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Preparation
