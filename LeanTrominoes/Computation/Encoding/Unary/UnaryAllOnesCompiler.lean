/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Unary.UnaryExactOneBooleanCompiler
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldAggregateCompiler
import LeanTrominoes.Computation.Encoding.Encoded.EncodedUnaryColumnLogicCompiler

/-! # A polynomial-time universal exact-one test on unary fields -/
noncomputable section
namespace LeanTrominoes.UnaryAllOnes
open _root_.Computability Turing
open UnaryFieldEncoderMachine (unaryFields unaryField)

def allOnes (values : List Nat) : Bool := decide (∀ value ∈ values, value=1)

def failures (values : List Nat) : List Nat :=
  values.map fun value => (!(decide (value=1))).toNat

theorem failures_sum_zero (values : List Nat) :
    (failures values).sum=0 ↔ ∀ value ∈ values, value=1 := by
  induction values with
  | nil => simp [failures]
  | cons value rest ih =>
    by_cases same : value=1 <;> simp_all [failures]

def failuresCompiler : TM2ComputableInPolyTime unaryFields unaryFields failures := by
  let physical := TM2CompositionMachine.computableInPolyTime
    UnaryExactOneBooleans.bitsComputableInPolyTime
    (FiniteBlockTransducer.computableInPolyTime (fun bit : Bool => unaryField ((!bit).toNat)))
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro values
  simp [UnaryExactOneBooleans.bits_eq_map,failures,unaryFields,List.flatMap_map]

def compiler : TM2ComputableInPolyTime unaryFields (fun bit => [bit]) allOnes := by
  let totals := TM2CompositionMachine.computableInPolyTime failuresCompiler UnaryFieldAggregate.sumCompiler
  let zeros := TM2CompositionMachine.computableInPolyTime totals EncodedUnaryColumn.zeroIndicatorsCompiler
  let physical := TM2CompositionMachine.computableInPolyTime zeros UnaryExactOneBooleans.bitsComputableInPolyTime
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro values
  simp [UnaryExactOneBooleans.bits_eq_map,EncodedUnaryColumn.zeroIndicators,allOnes,failures_sum_zero]

end LeanTrominoes.UnaryAllOnes
end
