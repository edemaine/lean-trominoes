/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairData
import LeanTrominoes.UnaryFieldPairPresenceCompiler

/-! # Row and column bits of rank-ordered carrier fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open CarrierRankDatumCompiledFields

/-- For every ordered datum pair, whether the selected endpoint field is
strictly positive. -/
def fieldPresenceBits (side : UnaryFieldPairPresence.Side)
    (field : Field) (descriptors : List RouteDescriptor) : List Bool :=
  UnaryFieldPairPresence.fieldBits side
    (field.rankOrderedValues descriptors)

/-- For every ordered datum pair, whether the selected endpoint field is
zero. -/
def fieldZeroBits (side : UnaryFieldPairPresence.Side)
    (field : Field) (descriptors : List RouteDescriptor) : List Bool :=
  AlignedBooleanListClosure.negated
    (fieldPresenceBits side field descriptors)

/-- Axis bit contributed by the first endpoint. -/
def axisBits : List RouteDescriptor → List Bool :=
  fieldPresenceBits .first .horizontal

/-- Whether the first endpoint is a crossing boundary. -/
def firstBoundaryBits : List RouteDescriptor → List Bool :=
  fieldPresenceBits .first .boundaryPresence

/-- Whether the second endpoint is a crossing boundary. -/
def secondBoundaryBits : List RouteDescriptor → List Bool :=
  fieldPresenceBits .second .boundaryPresence

@[simp] theorem fieldPresenceBits_length
    (side : UnaryFieldPairPresence.Side) (field : Field)
    (descriptors : List RouteDescriptor) :
    (fieldPresenceBits side field descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [fieldPresenceBits]

@[simp] theorem fieldZeroBits_length
    (side : UnaryFieldPairPresence.Side) (field : Field)
    (descriptors : List RouteDescriptor) :
    (fieldZeroBits side field descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [fieldZeroBits]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
