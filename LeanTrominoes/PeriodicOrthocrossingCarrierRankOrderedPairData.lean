/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedBooleanListClosure
import LeanTrominoes.DelimitedBinaryWordPairExcessMachine
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldData
import LeanTrominoes.SignedUnaryEqualityCompiler
import LeanTrominoes.UnaryExactOneBooleanCompiler
import LeanTrominoes.UnaryFieldBinaryWordCompiler
import LeanTrominoes.UnaryFieldEqualityRowsCompiler
import LeanTrominoes.UnaryFieldRangeCompiler
import LeanTrominoes.UnaryPermutationRankLookupLength

/-! # Candidate pairs over globally rank-ordered carrier data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open CarrierRankDatumCompiledFields

abbrev InputEncoding := CarrierRankGlobal.InputEncoding

def fieldEqualityBits
    (field : CarrierRankDatumCompiledFields.Field)
    (descriptors : List RouteDescriptor) : List Bool :=
  UnaryFieldEqualityRows.equalityBits (field.rankOrderedValues descriptors)

def horizontalTranslationEqualityBits
    (descriptors : List RouteDescriptor) : List Bool :=
  SignedUnaryEquality.equalityBits
    (Field.rankOrderedValues .keyTranslateHorizontalPositive descriptors)
    (Field.rankOrderedValues .keyTranslateHorizontalNegative descriptors)

def verticalTranslationEqualityBits
    (descriptors : List RouteDescriptor) : List Bool :=
  SignedUnaryEquality.equalityBits
    (Field.rankOrderedValues .keyTranslateVerticalPositive descriptors)
    (Field.rankOrderedValues .keyTranslateVerticalNegative descriptors)

def combined (first second : List Bool) : List Bool :=
  List.zipWith (· && ·) first second

def indexEqualityBits (descriptors : List RouteDescriptor) : List Bool :=
  combined (fieldEqualityBits .keyRoute descriptors)
    (fieldEqualityBits .keySegment descriptors)

def translationEqualityBits
    (descriptors : List RouteDescriptor) : List Bool :=
  combined (horizontalTranslationEqualityBits descriptors)
    (verticalTranslationEqualityBits descriptors)

/-- Equality of the complete six-field carrier key for every ordered pair in
global rank order. -/
def sameKeyBits (descriptors : List RouteDescriptor) : List Bool :=
  combined (indexEqualityBits descriptors)
    (translationEqualityBits descriptors)

/-- Canonical positions aligned with the globally rank-ordered data. -/
def positions (descriptors : List RouteDescriptor) : List Nat :=
  UnaryFieldRange.values (Field.rankOrderedValues .keyRoute descriptors)

def positionWordPairs (descriptors : List RouteDescriptor) :
    DelimitedBinaryWordPairs.Input :=
  DelimitedBinaryWordPairProductMachine.pairs
    (UnaryFieldBinaryWords.words (positions descriptors))

/-- For every ordered position pair, `second - first` in unary. -/
def positionExcesses (descriptors : List RouteDescriptor) : List Nat :=
  DelimitedBinaryWordPairExcessMachine.excesses false
    (positionWordPairs descriptors)

/-- The row-major predicate that the second global position immediately
follows the first. -/
def successorBits (descriptors : List RouteDescriptor) : List Bool :=
  UnaryExactOneBooleans.bits (positionExcesses descriptors)

/-- Row-major candidate pairs that are consecutive positions within one
carrier-key block. -/
def bits (descriptors : List RouteDescriptor) : List Bool :=
  combined (sameKeyBits descriptors) (successorBits descriptors)

@[simp] theorem rankOrderedValues_length
    (field : CarrierRankDatumCompiledFields.Field)
    (descriptors : List RouteDescriptor) :
    (field.rankOrderedValues descriptors).length =
      (UnaryPermutationRankLookup.extendedRanks
        (CarrierRankGlobal.ranks descriptors)).dedup.length := by
  simp [CarrierRankDatumCompiledFields.Field.rankOrderedValues]

theorem rankOrderedValues_lengths_eq
    (first second : CarrierRankDatumCompiledFields.Field)
    (descriptors : List RouteDescriptor) :
    (first.rankOrderedValues descriptors).length =
      (second.rankOrderedValues descriptors).length := by
  simp

@[simp] theorem fieldEqualityBits_length
    (field : CarrierRankDatumCompiledFields.Field)
    (descriptors : List RouteDescriptor) :
    (fieldEqualityBits field descriptors).length =
      (CarrierRankDatumCompiledFields.Field.rankOrderedValues
        .keyRoute descriptors).length ^ 2 := by
  simp [fieldEqualityBits]

@[simp] theorem horizontalTranslationEqualityBits_length
    (descriptors : List RouteDescriptor) :
    (horizontalTranslationEqualityBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  unfold horizontalTranslationEqualityBits
  rw [SignedUnaryEquality.equalityBits_length
    (rankOrderedValues_lengths_eq
      .keyTranslateHorizontalPositive .keyTranslateHorizontalNegative
      descriptors)]
  simp

@[simp] theorem verticalTranslationEqualityBits_length
    (descriptors : List RouteDescriptor) :
    (verticalTranslationEqualityBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  unfold verticalTranslationEqualityBits
  rw [SignedUnaryEquality.equalityBits_length
    (rankOrderedValues_lengths_eq
      .keyTranslateVerticalPositive .keyTranslateVerticalNegative
      descriptors)]
  simp

@[simp] theorem indexEqualityBits_length
    (descriptors : List RouteDescriptor) :
    (indexEqualityBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [indexEqualityBits, combined]

@[simp] theorem translationEqualityBits_length
    (descriptors : List RouteDescriptor) :
    (translationEqualityBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [translationEqualityBits, combined]

@[simp] theorem sameKeyBits_length (descriptors : List RouteDescriptor) :
    (sameKeyBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [sameKeyBits, indexEqualityBits, translationEqualityBits, combined,
    horizontalTranslationEqualityBits, verticalTranslationEqualityBits]

@[simp] theorem positions_length (descriptors : List RouteDescriptor) :
    (positions descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length := by
  simp [positions, UnaryFieldRange.values]

private theorem orderedProduct_length {Value : Type*}
    (values : List Value) :
    (values.flatMap fun first =>
      values.map fun second => (first, second)).length = values.length ^ 2 := by
  simp [pow_two]

@[simp] theorem successorBits_length (descriptors : List RouteDescriptor) :
    (successorBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  unfold successorBits positionExcesses positionWordPairs
  rw [UnaryExactOneBooleans.bits_length]
  rw [show
    (DelimitedBinaryWordPairExcessMachine.excesses false
      (DelimitedBinaryWordPairProductMachine.pairs
        (UnaryFieldBinaryWords.words (positions descriptors)))).length =
      (DelimitedBinaryWordPairProductMachine.pairs
        (UnaryFieldBinaryWords.words (positions descriptors))).pairs.length
    by simp [DelimitedBinaryWordPairExcessMachine.excesses]]
  unfold DelimitedBinaryWordPairProductMachine.pairs
  rw [orderedProduct_length]
  simp [UnaryFieldBinaryWords.words]

@[simp] theorem bits_length (descriptors : List RouteDescriptor) :
    (bits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [bits, combined]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
