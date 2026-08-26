/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairData
import LeanTrominoes.SignedUnarySuccessorData

/-! # Next-slice bits of rank-ordered carrier pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open CarrierRankDatumCompiledFields

/-- Whether the second horizontal normalization offset is the signed
successor of the first. -/
def horizontalNextBits (descriptors : List RouteDescriptor) : List Bool :=
  SignedUnarySuccessor.bits
    (Field.rankOrderedValues .normalizationHorizontalPositive descriptors)
    (Field.rankOrderedValues .normalizationHorizontalNegative descriptors)

/-- Whether both vertical normalization offsets are equal. -/
def verticalSameBits (descriptors : List RouteDescriptor) : List Bool :=
  SignedUnaryEquality.equalityBits
    (Field.rankOrderedValues .normalizationVerticalPositive descriptors)
    (Field.rankOrderedValues .normalizationVerticalNegative descriptors)

/-- Whether the second endpoint lies one normalized horizontal slice after
the first. -/
def nextSliceBits (descriptors : List RouteDescriptor) : List Bool :=
  combined
    (horizontalNextBits descriptors)
    (verticalSameBits descriptors)

@[simp] theorem horizontalNextBits_length
    (descriptors : List RouteDescriptor) :
    (horizontalNextBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  unfold horizontalNextBits
  rw [SignedUnarySuccessor.bits_length
    (rankOrderedValues_lengths_eq
      .normalizationHorizontalPositive
      .normalizationHorizontalNegative descriptors)]
  simp

@[simp] theorem verticalSameBits_length
    (descriptors : List RouteDescriptor) :
    (verticalSameBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  unfold verticalSameBits
  rw [SignedUnaryEquality.equalityBits_length
    (rankOrderedValues_lengths_eq
      .normalizationVerticalPositive
      .normalizationVerticalNegative descriptors)]
  simp

@[simp] theorem nextSliceBits_length
    (descriptors : List RouteDescriptor) :
    (nextSliceBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [nextSliceBits, combined]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
