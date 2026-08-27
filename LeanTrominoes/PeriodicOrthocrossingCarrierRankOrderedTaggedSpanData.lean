/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedMaskedSpanData

/-! # Axis-tagged retained carrier spans -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

def doubledOrderSpans (descriptors : List RouteDescriptor) : List Nat :=
  AlignedUnaryListClosure.added
    (orderSpans descriptors) (orderSpans descriptors)

def maskedDoubledSpanCodes
    (descriptors : List RouteDescriptor) : List Nat :=
  maskedSpanCodes
    (doubledOrderSpans descriptors) (retainedMaskBits descriptors)

/-- Zero rejects a matrix entry.  A retained vertical span `s` is encoded as
`2s + 2`; a retained horizontal span is encoded as the odd tag `2s + 3`. -/
def taggedSpanCodes (descriptors : List RouteDescriptor) : List Nat :=
  AlignedUnaryListClosure.added
    (maskedDoubledSpanCodes descriptors)
    (BooleanListUnaryFields.values (retainedAxisBits descriptors))

@[simp] theorem doubledOrderSpans_length
    (descriptors : List RouteDescriptor) :
    (doubledOrderSpans descriptors).length =
      (CarrierRankDatumCompiledFields.Field.rankOrderedValues
        .keyRoute descriptors).length ^ 2 := by
  simp [doubledOrderSpans]

@[simp] theorem maskedDoubledSpanCodes_length
    (descriptors : List RouteDescriptor) :
    (maskedDoubledSpanCodes descriptors).length =
      (CarrierRankDatumCompiledFields.Field.rankOrderedValues
        .keyRoute descriptors).length ^ 2 := by
  unfold maskedDoubledSpanCodes maskedSpanCodes
  rw [selectedValues_length]
  simp

@[simp] theorem taggedSpanCodes_length
    (descriptors : List RouteDescriptor) :
    (taggedSpanCodes descriptors).length =
      (CarrierRankDatumCompiledFields.Field.rankOrderedValues
        .keyRoute descriptors).length ^ 2 := by
  simp [taggedSpanCodes, BooleanListUnaryFields.values]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
