/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedBooleanListClosure
import LeanTrominoes.UnaryFieldPairPresenceCompiler
import LeanTrominoes.UnaryFieldStrictLowerRowsCompiler

/-! # Strict comparison matrices for signed unary fields -/

noncomputable section

namespace LeanTrominoes
namespace SignedUnaryStrictLower

open Computability Turing

def pairwise (operation : UnarySmallSumBooleans.Operation)
    (first second : List Bool) : List Bool :=
  List.zipWith operation.apply first second

def positiveLower (positive : List Nat) : List Bool :=
  UnaryFieldStrictLowerRows.strictLowerBits positive

def negativeUpper (negative : List Nat) : List Bool :=
  UnaryFieldStrictLowerRows.strictUpperBits negative

def firstNegative (negative : List Nat) : List Bool :=
  UnaryFieldPairPresence.fieldBits .first negative

def secondNegative (negative : List Nat) : List Bool :=
  UnaryFieldPairPresence.fieldBits .second negative

@[simp] theorem positiveLower_length (positive : List Nat) :
    (positiveLower positive).length = positive.length ^ 2 := by
  simp [positiveLower]

@[simp] theorem negativeUpper_length (negative : List Nat) :
    (negativeUpper negative).length = negative.length ^ 2 := by
  simp [negativeUpper]

def nonnegativeCase (positive negative : List Nat) : List Bool :=
  pairwise .conjunction
    (AlignedBooleanListClosure.negated (firstNegative negative))
    (pairwise .disjunction
      (secondNegative negative) (positiveLower positive))

def negativeCase (negative : List Nat) : List Bool :=
  pairwise .conjunction
    (firstNegative negative)
    (pairwise .conjunction
      (secondNegative negative) (negativeUpper negative))

/-- For canonical positive/negative magnitudes, mark exactly those ordered
pairs whose second signed value is smaller than their first signed value. -/
def strictLowerBits (positive negative : List Nat) : List Bool :=
  pairwise .disjunction
    (nonnegativeCase positive negative)
    (negativeCase negative)

@[simp] theorem firstNegative_length (negative : List Nat) :
    (firstNegative negative).length = negative.length ^ 2 := by
  simp [firstNegative]

@[simp] theorem secondNegative_length (negative : List Nat) :
    (secondNegative negative).length = negative.length ^ 2 := by
  simp [secondNegative]

@[simp] theorem pairwise_length (operation : UnarySmallSumBooleans.Operation)
    (first second : List Bool) :
    (pairwise operation first second).length =
      min first.length second.length := by
  simp [pairwise]

@[simp] theorem nonnegativeCase_length
    {positive negative : List Nat}
    (lengthEq : positive.length = negative.length) :
    (nonnegativeCase positive negative).length = positive.length ^ 2 := by
  simp [nonnegativeCase, lengthEq]

@[simp] theorem negativeCase_length (negative : List Nat) :
    (negativeCase negative).length = negative.length ^ 2 := by
  simp [negativeCase]

@[simp] theorem strictLowerBits_length
    {positive negative : List Nat}
    (lengthEq : positive.length = negative.length) :
    (strictLowerBits positive negative).length = positive.length ^ 2 := by
  simp [strictLowerBits, lengthEq]

/-- Any two aligned positive/negative unary-field compilers can be composed
into the signed strict-lower matrix used by stable carrier ranking. -/
noncomputable def strictLowerBitsComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (positive negative : Input → List Nat)
    (lengthEq : ∀ input,
      (positive input).length = (negative input).length)
    (positiveCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields positive)
    (negativeCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields negative) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => strictLowerBits
        (positive input) (negative input)) := by
  let positiveLowerCompiler :=
    UnaryFieldStrictLowerRows.bitsComputableInPolyTime
      encodeInput positive positiveCompiler
  let negativeUpperCompiler :=
    UnaryFieldStrictLowerRows.upperBitsComputableInPolyTime
      encodeInput negative negativeCompiler
  let firstNegativeCompiler :=
    UnaryFieldPairPresence.fieldBitsComputableInPolyTime
      encodeInput negative negativeCompiler .first
  let secondNegativeCompiler :=
    UnaryFieldPairPresence.fieldBitsComputableInPolyTime
      encodeInput negative negativeCompiler .second
  let notFirstNegativeCompiler :=
    AlignedBooleanListClosure.mapNegatedComputableInPolyTime
      encodeInput (fun input => firstNegative (negative input))
      firstNegativeCompiler
  let secondNegativeOrPositiveLowerCompiler :=
    AlignedBooleanListClosure.combinedComputableInPolyTime
      encodeInput .disjunction
      (fun input => secondNegative (negative input))
      (fun input => positiveLower (positive input))
      (fun input => by simp [lengthEq input])
      secondNegativeCompiler positiveLowerCompiler
  let nonnegativeCaseCompiler :=
    AlignedBooleanListClosure.combinedComputableInPolyTime
      encodeInput .conjunction
      (fun input =>
        AlignedBooleanListClosure.negated
          (firstNegative (negative input)))
      (fun input => pairwise .disjunction
        (secondNegative (negative input))
        (positiveLower (positive input)))
      (fun input => by simp [lengthEq input])
      notFirstNegativeCompiler secondNegativeOrPositiveLowerCompiler
  let secondNegativeAndUpperCompiler :=
    AlignedBooleanListClosure.combinedComputableInPolyTime
      encodeInput .conjunction
      (fun input => secondNegative (negative input))
      (fun input => negativeUpper (negative input))
      (fun input => by simp)
      secondNegativeCompiler negativeUpperCompiler
  let negativeCaseCompiler :=
    AlignedBooleanListClosure.combinedComputableInPolyTime
      encodeInput .conjunction
      (fun input => firstNegative (negative input))
      (fun input => pairwise .conjunction
        (secondNegative (negative input))
        (negativeUpper (negative input)))
      (fun input => by simp)
      firstNegativeCompiler secondNegativeAndUpperCompiler
  let combinedCompiler :=
    AlignedBooleanListClosure.combinedComputableInPolyTime
      encodeInput .disjunction
      (fun input => nonnegativeCase
        (positive input) (negative input))
      (fun input => negativeCase (negative input))
      (fun input => by simp [lengthEq input])
      nonnegativeCaseCompiler negativeCaseCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := id)
    (function₂ := fun input => strictLowerBits
      (positive input) (negative input))
    combinedCompiler (fun _ => rfl)

end SignedUnaryStrictLower
end LeanTrominoes

end
