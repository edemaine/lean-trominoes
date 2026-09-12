/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryIndexedValueLookupSemantics

/-! # Broadcasting the length of a compiled unit word into unary fields -/

noncomputable section
namespace LeanTrominoes.UnaryFieldUnitLengthBroadcast
open Computability Turing

/-- Append one delimiter to a unit word to obtain a single unary field. -/
noncomputable def singletonComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun units : List Unit => [units.length]) := by
  let unitsCompiler := FiniteBlockTransducer.computableInPolyTime
    (fun _ : Unit => [UnaryFieldEncoderMachine.Symbol.unit])
  let delimiterCompiler := TM2ConstantValueCompiler.computableInPolyTime
    (Input := List Unit) id id [UnaryFieldEncoderMachine.Symbol.delimiter]
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (TM2ListAppend.computableInPolyTime unitsCompiler delimiterCompiler) (fun units => by
      have unitsEq : units.flatMap (fun _ => [UnaryFieldEncoderMachine.Symbol.unit]) =
          List.replicate units.length UnaryFieldEncoderMachine.Symbol.unit := by
        induction units with
        | nil => rfl
        | cons marker units induction => simp [List.replicate_succ, induction]
      simp [UnaryFieldEncoderMachine.unaryFields,
        UnaryFieldEncoderMachine.unaryField, unitsEq])

/-- Query the sole length field once for every reference field. -/
def values (reference : List Nat) (units : List Unit) : List Nat :=
  UnaryIndexedValueLookup.values (UnaryFieldConstantStreams.zeros reference) [units.length]

theorem values_eq_map (reference : List Nat) (units : List Unit) :
    values reference units = reference.map (fun _ => units.length) := by
  unfold values
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt _ _ (by
    intro query member
    simp only [UnaryFieldConstantStreams.zeros, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member
    simp)]
  simp [UnaryFieldConstantStreams.zeros]

@[simp] theorem values_length (reference : List Nat) (units : List Unit) :
    (values reference units).length = reference.length := by
  rw [values_eq_map, List.length_map]

/-- A compiled unit word can supply a common field value to an independently
compiled reference column, including for an empty source alphabet. -/
noncomputable def nativeListComputableInPolyTime
    {Symbol : Type} [Fintype Symbol]
    (reference : List Symbol → List Nat) (units : List Symbol → List Unit)
    (referenceCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields reference)
    (unitsCompiler : TM2ComputableInPolyTime id id units) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun source => values (reference source) (units source)) := by
  classical
  exact if nonemptyAlphabet : Nonempty Symbol then by
    letI : Inhabited Symbol := ⟨Classical.choice nonemptyAlphabet⟩
    unfold values
    exact UnaryIndexedValueLookup.valuesComputableInPolyTime id _ _
      (TM2CompositionMachine.computableInPolyTime referenceCompiler
        UnaryFieldConstantStreams.zerosComputableInPolyTime)
      (TM2CompositionMachine.computableInPolyTime unitsCompiler singletonComputableInPolyTime)
  else by
    letI : IsEmpty Symbol := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.UnaryFieldUnitLengthBroadcast
end
