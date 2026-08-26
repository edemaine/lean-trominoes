/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairFieldBitData

/-! # Ownership bits of rank-ordered carrier pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

/-- Pointwise disjunction of aligned Boolean streams. -/
def disjoined (first second : List Bool) : List Bool :=
  List.zipWith (· || ·) first second

/-- Pointwise Boolean selection from two aligned streams. -/
def muxBits (selector whenTrue whenFalse : List Bool) : List Bool :=
  disjoined
    (combined selector whenTrue)
    (combined (AlignedBooleanListClosure.negated selector) whenFalse)

/-- Whether all four signed ownership magnitudes of the selected endpoint
are zero. -/
def endpointOwnershipZeroBits (side : UnaryFieldPairPresence.Side)
    (descriptors : List RouteDescriptor) : List Bool :=
  combined
    (combined
      (fieldZeroBits side .ownershipHorizontalPositive descriptors)
      (fieldZeroBits side .ownershipHorizontalNegative descriptors))
    (combined
      (fieldZeroBits side .ownershipVerticalPositive descriptors)
      (fieldZeroBits side .ownershipVerticalNegative descriptors))

def firstOwnershipZeroBits : List RouteDescriptor → List Bool :=
  endpointOwnershipZeroBits .first

def secondOwnershipZeroBits : List RouteDescriptor → List Bool :=
  endpointOwnershipZeroBits .second

/-- Whether each ordered pair uses a zero ownership shift, selecting the
first boundary, then the second boundary, then the first terminal. -/
def representativeBits (descriptors : List RouteDescriptor) : List Bool :=
  muxBits
    (firstBoundaryBits descriptors)
    (firstOwnershipZeroBits descriptors)
    (muxBits
      (secondBoundaryBits descriptors)
      (secondOwnershipZeroBits descriptors)
      (firstOwnershipZeroBits descriptors))

@[simp] theorem disjoined_length (first second : List Bool) :
    (disjoined first second).length = min first.length second.length := by
  simp [disjoined]

@[simp] theorem endpointOwnershipZeroBits_length
    (side : UnaryFieldPairPresence.Side)
    (descriptors : List RouteDescriptor) :
    (endpointOwnershipZeroBits side descriptors).length =
      (CarrierRankDatumCompiledFields.Field.rankOrderedValues
        .keyRoute descriptors).length ^ 2 := by
  simp [endpointOwnershipZeroBits, combined]

@[simp] theorem firstOwnershipZeroBits_length
    (descriptors : List RouteDescriptor) :
    (firstOwnershipZeroBits descriptors).length =
      (CarrierRankDatumCompiledFields.Field.rankOrderedValues
        .keyRoute descriptors).length ^ 2 := by
  simp [firstOwnershipZeroBits]

@[simp] theorem secondOwnershipZeroBits_length
    (descriptors : List RouteDescriptor) :
    (secondOwnershipZeroBits descriptors).length =
      (CarrierRankDatumCompiledFields.Field.rankOrderedValues
        .keyRoute descriptors).length ^ 2 := by
  simp [secondOwnershipZeroBits]

@[simp] theorem representativeBits_length
    (descriptors : List RouteDescriptor) :
    (representativeBits descriptors).length =
      (CarrierRankDatumCompiledFields.Field.rankOrderedValues
        .keyRoute descriptors).length ^ 2 := by
  simp [representativeBits, muxBits, combined, firstBoundaryBits,
    secondBoundaryBits]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
