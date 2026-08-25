/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BooleanListUnaryFieldCompiler
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryAlignedAddTime
import LeanTrominoes.UnaryAlignedAddValidity
import LeanTrominoes.UnarySmallSumBooleanCompiler

/-! # Polynomial-time pointwise Boolean-list operations -/

noncomputable section

namespace LeanTrominoes
namespace AlignedBooleanListClosure

open Computability Turing

def negated (bits : List Bool) : List Bool :=
  bits.map (!·)

@[simp] theorem negated_length (bits : List Bool) :
    (negated bits).length = bits.length := by
  simp [negated]

def negatedTokens (bits : List Bool) : List Bool :=
  bits.flatMap fun bit => [!bit]

theorem negatedTokens_eq (bits : List Bool) :
    negatedTokens bits = negated bits := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [negatedTokens, List.flatMap_cons, negated,
        List.map_cons, List.singleton_append]
      rw [show List.flatMap (fun current => [!current]) bits =
          negatedTokens bits by rfl,
        induction]
      rfl

noncomputable def negatedComputableInPolyTime :
    TM2ComputableInPolyTime id id negated := by
  let physical : TM2ComputableInPolyTime id id negatedTokens :=
    FiniteBlockTransducer.computableInPolyTime fun bit => [!bit]
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := id) (function₂ := negated)
    physical negatedTokens_eq

/-- Postcomposition by pointwise Boolean negation preserves polynomial time. -/
noncomputable def mapNegatedComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (bits : Input → List Bool)
    (compiler :
      @TM2ComputableInPolyTime
        Input (List Bool) InputSymbol Bool encodeInput id bits) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => negated (bits input)) :=
  TM2CompositionMachine.computableInPolyTime compiler
    negatedComputableInPolyTime

def additionInput (first second : List Bool)
    (lengthEq : first.length = second.length) :
    UnaryAlignedAddMachine.Input where
  firsts := BooleanListUnaryFields.values first
  seconds := BooleanListUnaryFields.values second
  valid := UnaryAlignedAddMachine.Valid.of_length_eq (by
    simpa [BooleanListUnaryFields.values] using lengthEq)

def combined (operation : UnarySmallSumBooleans.Operation)
    (first second : List Bool) : List Bool :=
  UnarySmallSumBooleans.bits operation
    (UnaryAlignedAddMachine.sums
      (BooleanListUnaryFields.values first)
      (BooleanListUnaryFields.values second))

theorem sumBit_bitNat
    (operation : UnarySmallSumBooleans.Operation)
    (first second : Bool) :
    UnarySmallSumBooleans.sumBit operation
        (BooleanListUnaryFields.bitNat first +
          BooleanListUnaryFields.bitNat second) =
      operation.apply first second := by
  cases operation <;> cases first <;> cases second <;> rfl

/-- The unary detour computes the ordinary pointwise Boolean operation. -/
theorem combined_eq_zipWith
    (operation : UnarySmallSumBooleans.Operation)
    (first second : List Bool)
    (lengthEq : first.length = second.length) :
    combined operation first second =
      List.zipWith operation.apply first second := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons second seconds => simp at lengthEq
  | cons first firsts induction =>
      cases second with
      | nil => simp at lengthEq
      | cons second seconds =>
          have tailLengthEq : firsts.length = seconds.length := by
            simpa using lengthEq
          simp only [combined, BooleanListUnaryFields.values,
            List.map_cons, UnaryAlignedAddMachine.sums,
            UnarySmallSumBooleans.bits, List.zipWith_cons_cons]
          rw [sumBit_bitNat]
          congr 1
          exact induction seconds tailLengthEq

/-- Equal-length Boolean streams produced from one input can be combined
pointwise by conjunction or disjunction in polynomial time. -/
noncomputable def combinedComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (operation : UnarySmallSumBooleans.Operation)
    (first second : Input → List Bool)
    (lengthEq : ∀ input, (first input).length = (second input).length)
    (firstCompiler :
      @TM2ComputableInPolyTime
        Input (List Bool) InputSymbol Bool encodeInput id first)
    (secondCompiler :
      @TM2ComputableInPolyTime
        Input (List Bool) InputSymbol Bool encodeInput id second) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => List.zipWith operation.apply
        (first input) (second input)) := by
  let firstUnary := TM2CompositionMachine.computableInPolyTime
    firstCompiler BooleanListUnaryFields.valuesComputableInPolyTime
  let secondUnary := TM2CompositionMachine.computableInPolyTime
    secondCompiler BooleanListUnaryFields.valuesComputableInPolyTime
  let paired := TM2ForkMachine.computableInPolyTime
    firstUnary secondUnary
  let prepared : TM2ComputableInPolyTime encodeInput
      UnaryAlignedAddMachine.encode
      (fun input => additionInput
        (first input) (second input) (lengthEq input)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
      (fun _ => rfl)
  let added := TM2CompositionMachine.computableInPolyTime prepared
    UnaryAlignedAddMachine.computableInPolyTime
  let combinedCompiler := TM2CompositionMachine.computableInPolyTime added
    (UnarySmallSumBooleans.bitsComputableInPolyTime operation)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := id)
    (function₂ := fun input => List.zipWith operation.apply
      (first input) (second input)) combinedCompiler
    (fun input => combined_eq_zipWith operation
      (first input) (second input) (lengthEq input))

end AlignedBooleanListClosure
end LeanTrominoes

end
