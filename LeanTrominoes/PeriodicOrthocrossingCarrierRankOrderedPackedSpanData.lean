/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedTaggedSpanData

/-! # Axis/next-slice-packed retained carrier spans -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

/-- Double the axis-tagged code.  For a retained span this is
`4 * span + 4 + 2 * axis`; rejected matrix entries remain zero. -/
def doubledTaggedSpanCodes
    (descriptors : List RouteDescriptor) : List Nat :=
  AlignedUnaryListClosure.added
    (taggedSpanCodes descriptors) (taggedSpanCodes descriptors)

/-- Zero rejects a matrix entry.  Every retained entry has code
`4 * span + 4 + 2 * axis + nextSlice`, so its residue modulo four stores
both finite carrier bits while its quotient stores `span + 1`. -/
def packedSpanCodes (descriptors : List RouteDescriptor) : List Nat :=
  AlignedUnaryListClosure.added
    (doubledTaggedSpanCodes descriptors)
    (BooleanListUnaryFields.values (retainedNextSliceBits descriptors))

/-- Unary tape representation of the packed fields. -/
def packedSpanStream (descriptors : List RouteDescriptor) :
    List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryFields (packedSpanCodes descriptors)

@[simp] theorem doubledTaggedSpanCodes_length
    (descriptors : List RouteDescriptor) :
    (doubledTaggedSpanCodes descriptors).length =
      (CarrierRankDatumCompiledFields.Field.rankOrderedValues
        .keyRoute descriptors).length ^ 2 := by
  simp [doubledTaggedSpanCodes]

@[simp] theorem packedSpanCodes_length
    (descriptors : List RouteDescriptor) :
    (packedSpanCodes descriptors).length =
      (CarrierRankDatumCompiledFields.Field.rankOrderedValues
        .keyRoute descriptors).length ^ 2 := by
  simp [packedSpanCodes, BooleanListUnaryFields.values]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
