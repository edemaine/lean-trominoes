/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsTime
import LeanTrominoes.DelimitedBinaryWordPairLengthComparisonTime
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldBinaryWordCompiler

/-! # Strict-lower comparison rows for unary fields -/

noncomputable section

namespace LeanTrominoes
namespace UnaryFieldStrictLowerRows

open Computability Turing
open DelimitedBinaryWordPairLengthComparisonMachine

/-- A row-major comparison contributes `true` exactly when its first unary
value is strictly greater than its second. -/
def orderingBit : LengthOrdering → Bool
  | .less | .equal => false
  | .greater => true

def orderingBits (orderings : List LengthOrdering) : List Bool :=
  orderings.flatMap fun ordering => [orderingBit ordering]

/-- The opposite orientation marks `first < second` in the same row-major
ordered product. -/
def reverseOrderingBit : LengthOrdering → Bool
  | .less => true
  | .equal | .greater => false

def reverseOrderingBits (orderings : List LengthOrdering) : List Bool :=
  orderings.flatMap fun ordering => [reverseOrderingBit ordering]

theorem orderingBits_eq_map (orderings : List LengthOrdering) :
    orderingBits orderings = orderings.map orderingBit := by
  induction orderings with
  | nil => rfl
  | cons ordering orderings induction =>
      simp only [orderingBits, List.flatMap_cons, List.map_cons,
        List.singleton_append]
      rw [show List.flatMap (fun current => [orderingBit current])
          orderings = orderingBits orderings by rfl,
        induction]

theorem reverseOrderingBits_eq_map (orderings : List LengthOrdering) :
    reverseOrderingBits orderings =
      orderings.map reverseOrderingBit := by
  induction orderings with
  | nil => rfl
  | cons ordering orderings induction =>
      simp only [reverseOrderingBits, List.flatMap_cons, List.map_cons,
        List.singleton_append]
      rw [show List.flatMap (fun current => [reverseOrderingBit current])
          orderings = reverseOrderingBits orderings by rfl,
        induction]

/-- Flat row-major matrix whose row for `first` marks every `second < first`. -/
def strictLowerBits (values : List Nat) : List Bool :=
  orderingBits
    (lengthOrderings
      (DelimitedBinaryWordPairProductMachine.pairs
        (UnaryFieldBinaryWords.words values)))

/-- Flat row-major matrix whose row for `first` marks every `first < second`. -/
def strictUpperBits (values : List Nat) : List Bool :=
  reverseOrderingBits
    (lengthOrderings
      (DelimitedBinaryWordPairProductMachine.pairs
        (UnaryFieldBinaryWords.words values)))

theorem orderingBit_compareNats (first second : Nat) :
    orderingBit (compareNats first second) = decide (second < first) := by
  induction first generalizing second with
  | zero =>
      cases second <;> rfl
  | succ first induction =>
      cases second with
      | zero => rfl
      | succ second =>
          simpa [compareNats] using induction second

theorem reverseOrderingBit_compareNats (first second : Nat) :
    reverseOrderingBit (compareNats first second) =
      decide (first < second) := by
  induction first generalizing second with
  | zero =>
      cases second <;> rfl
  | succ first induction =>
      cases second with
      | zero => rfl
      | succ second =>
          simpa [compareNats] using induction second

theorem strictLowerBits_eq_flatMap (values : List Nat) :
    strictLowerBits values =
      values.flatMap fun first =>
        values.map fun second => decide (second < first) := by
  unfold strictLowerBits
  rw [orderingBits_eq_map]
  unfold lengthOrderings
    DelimitedBinaryWordPairProductMachine.pairs
    UnaryFieldBinaryWords.words
  simp only [List.map_map, List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  simp [compareLengths, UnaryFieldBinaryWords.word,
    orderingBit_compareNats]

theorem strictUpperBits_eq_flatMap (values : List Nat) :
    strictUpperBits values =
      values.flatMap fun first =>
        values.map fun second => decide (first < second) := by
  unfold strictUpperBits
  rw [reverseOrderingBits_eq_map]
  unfold lengthOrderings
    DelimitedBinaryWordPairProductMachine.pairs
    UnaryFieldBinaryWords.words
  simp only [List.map_map, List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  simp [compareLengths, UnaryFieldBinaryWords.word,
    reverseOrderingBit_compareNats]

@[simp] theorem strictLowerBits_length (values : List Nat) :
    (strictLowerBits values).length = values.length ^ 2 := by
  rw [strictLowerBits_eq_flatMap]
  simp [pow_two]

@[simp] theorem strictUpperBits_length (values : List Nat) :
    (strictUpperBits values).length = values.length ^ 2 := by
  rw [strictUpperBits_eq_flatMap]
  simp [pow_two]

/-- The flat strict-order matrix with its machine-checkable square promise. -/
def squareInput (values : List Nat) : BoolSquareRows.Input where
  bits := strictLowerBits values
  square := by
    rw [strictLowerBits_length, Nat.sqrt_eq']

/-- Delimiter-separated strict-lower rows in the original value order. -/
def rows (values : List Nat) : DelimitedBinaryWords.Input :=
  (squareInput values).delimitedRows

noncomputable def orderingBitsComputableInPolyTime :
    TM2ComputableInPolyTime id id orderingBits :=
  FiniteBlockTransducer.computableInPolyTime fun ordering =>
    [orderingBit ordering]

noncomputable def reverseOrderingBitsComputableInPolyTime :
    TM2ComputableInPolyTime id id reverseOrderingBits :=
  FiniteBlockTransducer.computableInPolyTime fun ordering =>
    [reverseOrderingBit ordering]

/-- The same pair-comparison pipeline with the opposite orientation emits
the flat strict-upper matrix. -/
noncomputable def upperBitsComputableInPolyTime
    {Input InputSymbol : Type}
    (encodeInput : Input → List InputSymbol)
    (values : Input → List Nat)
    (valueCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields values) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => strictUpperBits (values input)) := by
  let wordCompiler := TM2CompositionMachine.computableInPolyTime
    valueCompiler UnaryFieldBinaryWords.wordsComputableInPolyTime
  let pairCompiler := TM2CompositionMachine.computableInPolyTime
    wordCompiler DelimitedBinaryWordPairProductMachine.computableInPolyTime
  let orderingCompiler := TM2CompositionMachine.computableInPolyTime
    pairCompiler
    DelimitedBinaryWordPairLengthComparisonMachine.computableInPolyTime
  let composed := TM2CompositionMachine.computableInPolyTime
    orderingCompiler reverseOrderingBitsComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := id)
    (function₂ := fun input => strictUpperBits (values input))
    composed (fun _ => rfl)

/-- Any unary-field compiler can be followed by the quadratic ordered-product
comparison pipeline to emit its flat strict-lower matrix. -/
noncomputable def bitsComputableInPolyTime
    {Input InputSymbol : Type}
    (encodeInput : Input → List InputSymbol)
    (values : Input → List Nat)
    (valueCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields values) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => strictLowerBits (values input)) := by
  let wordCompiler := TM2CompositionMachine.computableInPolyTime
    valueCompiler UnaryFieldBinaryWords.wordsComputableInPolyTime
  let pairCompiler := TM2CompositionMachine.computableInPolyTime
    wordCompiler DelimitedBinaryWordPairProductMachine.computableInPolyTime
  let orderingCompiler := TM2CompositionMachine.computableInPolyTime
    pairCompiler
    DelimitedBinaryWordPairLengthComparisonMachine.computableInPolyTime
  let bitCompiler := TM2CompositionMachine.computableInPolyTime
    orderingCompiler orderingBitsComputableInPolyTime
  exact bitCompiler

/-- The flat strict-order matrix can be reshaped into one delimited row per
input field without changing its polynomial-time bound. -/
noncomputable def rowsComputableInPolyTime
    {Input InputSymbol : Type}
    (encodeInput : Input → List InputSymbol)
    (values : Input → List Nat)
    (valueCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields values) :
    @TM2ComputableInPolyTime
      Input DelimitedBinaryWords.Input InputSymbol
      DelimitedBinaryWords.Token
      encodeInput DelimitedBinaryWords.finEncoding.encode
      (fun input => rows (values input)) := by
  let squareCompiler : @TM2ComputableInPolyTime
      Input BoolSquareRows.Input InputSymbol Bool
      encodeInput BoolSquareRows.finEncoding.encode
      (fun input => squareInput (values input)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      (encodeOutput₂ := BoolSquareRows.finEncoding.encode)
      (function₂ := fun input => squareInput (values input))
      (bitsComputableInPolyTime encodeInput values valueCompiler)
      (fun _ => rfl)
  let rowCompiler := TM2CompositionMachine.computableInPolyTime
    squareCompiler BoolSquareRowsMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := DelimitedBinaryWords.finEncoding.encode)
    (function₂ := fun input => rows (values input)) rowCompiler
    (fun _ => rfl)

end UnaryFieldStrictLowerRows
end LeanTrominoes

end
