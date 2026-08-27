/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairSpanData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairData
import LeanTrominoes.UnaryFieldConstantOffsetCompiler
import LeanTrominoes.UnarySuccessorEqualityFilterInput

/-! # Axis-masked spans of retained carrier pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

def verticalMaskBits (descriptors : List RouteDescriptor) : List Bool :=
  combined (retainedMaskBits descriptors)
    (AlignedBooleanListClosure.negated (axisBits descriptors))

def spanFilterRanks (spans : List Nat) : List Nat :=
  UnaryFieldConstantOffsets.values 1 spans

def spanFilterBaseSizes (spans : List Nat) : List Nat :=
  UnaryFieldConstantOffsets.values 2 spans

def inactiveMaskValues (mask : List Bool) : List Nat :=
  BooleanListUnaryFields.values
    (AlignedBooleanListClosure.negated mask)

def spanFilterSizes (spans : List Nat) (mask : List Bool) : List Nat :=
  AlignedUnaryListClosure.added
    (spanFilterBaseSizes spans) (inactiveMaskValues mask)

private def spanFilterValid :
    ∀ (spans : List Nat) (mask : List Bool),
      spans.length = mask.length →
      UnarySuccessorEqualityFilterMachine.Valid
        (spanFilterRanks spans) (spanFilterSizes spans mask)
  | [], [], _ => .nil
  | [], _ :: _, lengthEq => by simp at lengthEq
  | _ :: _, [], lengthEq => by simp at lengthEq
  | span :: spans, active :: mask, lengthEq => by
      apply UnarySuccessorEqualityFilterMachine.Valid.cons
      · cases active <;>
          simp [BooleanListUnaryFields.bitNat]
      · exact spanFilterValid spans mask (by simpa using lengthEq)

def spanFilterInput (spans : List Nat) (mask : List Bool)
    (lengthEq : spans.length = mask.length) :
    UnarySuccessorEqualityFilterMachine.Input where
  ranks := spanFilterRanks spans
  sizes := spanFilterSizes spans mask
  valid := spanFilterValid spans mask lengthEq

/-- Selected entries contain `span + 2`; rejected entries contain zero. -/
def maskedSpanCodes (spans : List Nat) (mask : List Bool) : List Nat :=
  UnarySuccessorEqualityFilterMachine.selectedValues
    (spanFilterRanks spans) (spanFilterSizes spans mask)

def horizontalSpanCodes (descriptors : List RouteDescriptor) : List Nat :=
  maskedSpanCodes (orderSpans descriptors) (retainedAxisBits descriptors)

def verticalSpanCodes (descriptors : List RouteDescriptor) : List Nat :=
  maskedSpanCodes (orderSpans descriptors) (verticalMaskBits descriptors)

private theorem selectedValues_length (ranks sizes : List Nat) :
    (UnarySuccessorEqualityFilterMachine.selectedValues ranks sizes).length =
      ranks.length := by
  induction ranks generalizing sizes with
  | nil => rfl
  | cons rank ranks induction =>
      cases sizes <;>
        simp [UnarySuccessorEqualityFilterMachine.selectedValues, induction]

@[simp] theorem verticalMaskBits_length
    (descriptors : List RouteDescriptor) :
    (verticalMaskBits descriptors).length =
      (CarrierRankDatumCompiledFields.Field.rankOrderedValues
        .keyRoute descriptors).length ^ 2 := by
  simp [verticalMaskBits, combined, axisBits]

@[simp] theorem spanFilterRanks_length (spans : List Nat) :
    (spanFilterRanks spans).length = spans.length := by
  simp [spanFilterRanks, UnaryFieldConstantOffsets.values]

@[simp] theorem spanFilterBaseSizes_length (spans : List Nat) :
    (spanFilterBaseSizes spans).length = spans.length := by
  simp [spanFilterBaseSizes, UnaryFieldConstantOffsets.values]

@[simp] theorem inactiveMaskValues_length (mask : List Bool) :
    (inactiveMaskValues mask).length = mask.length := by
  simp [inactiveMaskValues, BooleanListUnaryFields.values]

@[simp] theorem spanFilterSizes_length (spans : List Nat)
    (mask : List Bool) :
    (spanFilterSizes spans mask).length = min spans.length mask.length := by
  simp [spanFilterSizes]

@[simp] theorem horizontalSpanCodes_length
    (descriptors : List RouteDescriptor) :
    (horizontalSpanCodes descriptors).length =
      (CarrierRankDatumCompiledFields.Field.rankOrderedValues
        .keyRoute descriptors).length ^ 2 := by
  unfold horizontalSpanCodes maskedSpanCodes
  rw [selectedValues_length]
  simp

@[simp] theorem verticalSpanCodes_length
    (descriptors : List RouteDescriptor) :
    (verticalSpanCodes descriptors).length =
      (CarrierRankDatumCompiledFields.Field.rankOrderedValues
        .keyRoute descriptors).length ^ 2 := by
  unfold verticalSpanCodes maskedSpanCodes
  rw [selectedValues_length]
  simp

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
