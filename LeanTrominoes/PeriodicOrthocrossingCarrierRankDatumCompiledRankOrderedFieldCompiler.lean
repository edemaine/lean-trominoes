/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledColumnCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFieldLength
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalCompiler
import LeanTrominoes.UnaryPermutationRankLookupCompiler

/-! # Compiler for carrier rank-datum fields in global-rank order -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

open Computability Turing

/-- Each of the fifty presentation-order carrier datum fields is computable
in polynomial time. -/
noncomputable def Field.valuesComputableInPolyTime :
    (field : Field) →
      TM2ComputableInPolyTime descriptorInputEncoding
        UnaryFieldEncoderMachine.unaryFields field.values
  | .keyRoute => CarrierRankKeyRouteField.valuesComputableInPolyTime
  | .keySegment => CarrierRankKeySegmentField.valuesComputableInPolyTime
  | .keyTranslateHorizontalPositive =>
      CarrierRankKeySignedFields.horizontalPositiveValuesComputableInPolyTime
  | .keyTranslateHorizontalNegative =>
      CarrierRankKeySignedFields.horizontalNegativeValuesComputableInPolyTime
  | .keyTranslateVerticalPositive =>
      CarrierRankKeySignedFields.verticalPositiveValuesComputableInPolyTime
  | .keyTranslateVerticalNegative =>
      CarrierRankKeySignedFields.verticalNegativeValuesComputableInPolyTime
  | .orderPositive =>
      CarrierRankOrderField.valuesComputableInPolyTime true
  | .orderNegative =>
      CarrierRankOrderField.valuesComputableInPolyTime false
  | .horizontal => CarrierRankHorizontalField.valuesComputableInPolyTime
  | .normalizationHorizontalPositive =>
      CarrierNormalizationOffsetField.valuesComputableInPolyTime
        .horizontalPositive
  | .normalizationHorizontalNegative =>
      CarrierNormalizationOffsetField.valuesComputableInPolyTime
        .horizontalNegative
  | .normalizationVerticalPositive =>
      CarrierNormalizationOffsetField.valuesComputableInPolyTime
        .verticalPositive
  | .normalizationVerticalNegative =>
      CarrierNormalizationOffsetField.valuesComputableInPolyTime
        .verticalNegative
  | .boundaryPresence =>
      CarrierBoundaryPresenceField.valuesComputableInPolyTime
  | .crossingFirstRoute =>
      CarrierCrossingRecordSourceField.valuesComputableInPolyTime .firstRoute
  | .crossingFirstSegment =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        .firstSegmentIndex
  | .crossingFirstStartHorizontalPositive =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .first .start true true)
  | .crossingFirstStartHorizontalNegative =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .first .start true false)
  | .crossingFirstStartVerticalPositive =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .first .start false true)
  | .crossingFirstStartVerticalNegative =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .first .start false false)
  | .crossingFirstFinishHorizontalPositive =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .first .finish true true)
  | .crossingFirstFinishHorizontalNegative =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .first .finish true false)
  | .crossingFirstFinishVerticalPositive =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .first .finish false true)
  | .crossingFirstFinishVerticalNegative =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .first .finish false false)
  | .crossingFirstTranslateHorizontalPositive =>
      CarrierCrossingRecordSourceField.valuesComputableInPolyTime
        .firstTranslateHorizontalPositive
  | .crossingFirstTranslateHorizontalNegative =>
      CarrierCrossingRecordSourceField.valuesComputableInPolyTime
        .firstTranslateHorizontalNegative
  | .crossingFirstTranslateVerticalPositive =>
      CarrierCrossingRecordSourceField.valuesComputableInPolyTime
        .firstTranslateVerticalPositive
  | .crossingFirstTranslateVerticalNegative =>
      CarrierCrossingRecordSourceField.valuesComputableInPolyTime
        .firstTranslateVerticalNegative
  | .crossingSecondRoute =>
      CarrierCrossingRecordSourceField.valuesComputableInPolyTime .secondRoute
  | .crossingSecondSegment =>
      CarrierCrossingRecordSourceField.valuesComputableInPolyTime .secondSegment
  | .crossingSecondStartHorizontalPositive =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .second .start true true)
  | .crossingSecondStartHorizontalNegative =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .second .start true false)
  | .crossingSecondStartVerticalPositive =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .second .start false true)
  | .crossingSecondStartVerticalNegative =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .second .start false false)
  | .crossingSecondFinishHorizontalPositive =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .second .finish true true)
  | .crossingSecondFinishHorizontalNegative =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .second .finish true false)
  | .crossingSecondFinishVerticalPositive =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .second .finish false true)
  | .crossingSecondFinishVerticalNegative =>
      CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
        (.coordinate .second .finish false false)
  | .crossingSecondTranslateHorizontalPositive =>
      CarrierCrossingRecordSourceField.valuesComputableInPolyTime
        .secondTranslateHorizontalPositive
  | .crossingSecondTranslateHorizontalNegative =>
      CarrierCrossingRecordSourceField.valuesComputableInPolyTime
        .secondTranslateHorizontalNegative
  | .crossingSecondTranslateVerticalPositive =>
      CarrierCrossingRecordSourceField.valuesComputableInPolyTime
        .secondTranslateVerticalPositive
  | .crossingSecondTranslateVerticalNegative =>
      CarrierCrossingRecordSourceField.valuesComputableInPolyTime
        .secondTranslateVerticalNegative
  | .crossingPointHorizontalPositive =>
      CarrierCrossingPointField.valuesComputableInPolyTime .horizontalPositive
  | .crossingPointHorizontalNegative =>
      CarrierCrossingPointField.valuesComputableInPolyTime .horizontalNegative
  | .crossingPointVerticalPositive =>
      CarrierCrossingPointField.valuesComputableInPolyTime .verticalPositive
  | .crossingPointVerticalNegative =>
      CarrierCrossingPointField.valuesComputableInPolyTime .verticalNegative
  | .ownershipHorizontalPositive =>
      CarrierOwnershipShiftField.valuesComputableInPolyTime
        .horizontalPositive
  | .ownershipHorizontalNegative =>
      CarrierOwnershipShiftField.valuesComputableInPolyTime
        .horizontalNegative
  | .ownershipVerticalPositive =>
      CarrierOwnershipShiftField.valuesComputableInPolyTime .verticalPositive
  | .ownershipVerticalNegative =>
      CarrierOwnershipShiftField.valuesComputableInPolyTime .verticalNegative

/-- Reorder any of the fifty compiled carrier fields into global rank order
in polynomial time. -/
noncomputable def Field.rankOrderedValuesComputableInPolyTime
    (field : Field) :
    TM2ComputableInPolyTime descriptorInputEncoding
      UnaryFieldEncoderMachine.unaryFields field.rankOrderedValues := by
  change TM2ComputableInPolyTime descriptorInputEncoding
    UnaryFieldEncoderMachine.unaryFields fun descriptors =>
      UnaryPermutationRankLookup.values
        (CarrierRankGlobal.ranks descriptors) (field.values descriptors)
  exact UnaryPermutationRankLookup.valuesComputableInPolyTime
    descriptorInputEncoding CarrierRankGlobal.ranks field.values
    (Field.values_length_eq_ranks field)
    CarrierRankGlobal.ranksComputableInPolyTime
    field.valuesComputableInPolyTime

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing

end
