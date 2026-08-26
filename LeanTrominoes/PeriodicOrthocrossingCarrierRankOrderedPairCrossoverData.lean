/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairFieldBitData

/-! # Crossover tests on rank-ordered carrier pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open CarrierRankDatumCompiledFields

/-- Pointwise conjunction of equality matrices for a nonempty fixed field
list. -/
def fieldEqualityConjunction (field : Field) :
    List Field → List RouteDescriptor → List Bool
  | [], descriptors => fieldEqualityBits field descriptors
  | next :: rest, descriptors =>
      combined
        (fieldEqualityBits field descriptors)
        (fieldEqualityConjunction next rest descriptors)

/-- Crossing-payload fields fifteen through forty-five, after the leading
field fourteen. -/
def crossingPayloadTail : List Field :=
  [.crossingFirstSegment,
    .crossingFirstStartHorizontalPositive,
    .crossingFirstStartHorizontalNegative,
    .crossingFirstStartVerticalPositive,
    .crossingFirstStartVerticalNegative,
    .crossingFirstFinishHorizontalPositive,
    .crossingFirstFinishHorizontalNegative,
    .crossingFirstFinishVerticalPositive,
    .crossingFirstFinishVerticalNegative,
    .crossingFirstTranslateHorizontalPositive,
    .crossingFirstTranslateHorizontalNegative,
    .crossingFirstTranslateVerticalPositive,
    .crossingFirstTranslateVerticalNegative,
    .crossingSecondRoute,
    .crossingSecondSegment,
    .crossingSecondStartHorizontalPositive,
    .crossingSecondStartHorizontalNegative,
    .crossingSecondStartVerticalPositive,
    .crossingSecondStartVerticalNegative,
    .crossingSecondFinishHorizontalPositive,
    .crossingSecondFinishHorizontalNegative,
    .crossingSecondFinishVerticalPositive,
    .crossingSecondFinishVerticalNegative,
    .crossingSecondTranslateHorizontalPositive,
    .crossingSecondTranslateHorizontalNegative,
    .crossingSecondTranslateVerticalPositive,
    .crossingSecondTranslateVerticalNegative,
    .crossingPointHorizontalPositive,
    .crossingPointHorizontalNegative,
    .crossingPointVerticalPositive,
    .crossingPointVerticalNegative]

/-- Equality of all thirty-two crossing payload fields. -/
def crossingPayloadEqualityBits : List RouteDescriptor → List Bool :=
  fieldEqualityConjunction .crossingFirstRoute crossingPayloadTail

/-- Whether both endpoints are boundaries carrying the same crossing
payload. -/
def sameCrossoverBits (descriptors : List RouteDescriptor) : List Bool :=
  combined
    (combined
      (firstBoundaryBits descriptors)
      (secondBoundaryBits descriptors))
    (crossingPayloadEqualityBits descriptors)

/-- Whether an ordered pair is not internal to one crossover gadget. -/
def differentCrossoverBits (descriptors : List RouteDescriptor) : List Bool :=
  AlignedBooleanListClosure.negated (sameCrossoverBits descriptors)

@[simp] theorem fieldEqualityConjunction_length
    (field : Field) (rest : List Field)
    (descriptors : List RouteDescriptor) :
    (fieldEqualityConjunction field rest descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  induction rest generalizing field with
  | nil => simp [fieldEqualityConjunction]
  | cons next rest induction =>
      simp [fieldEqualityConjunction, combined, induction]

@[simp] theorem crossingPayloadEqualityBits_length
    (descriptors : List RouteDescriptor) :
    (crossingPayloadEqualityBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [crossingPayloadEqualityBits]

@[simp] theorem sameCrossoverBits_length
    (descriptors : List RouteDescriptor) :
    (sameCrossoverBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [sameCrossoverBits, combined, firstBoundaryBits,
    secondBoundaryBits]

@[simp] theorem differentCrossoverBits_length
    (descriptors : List RouteDescriptor) :
    (differentCrossoverBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [differentCrossoverBits]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
