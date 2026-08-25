/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentFieldLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointFieldLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetFieldLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftFieldLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankHorizontalFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyRouteFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeySegmentFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeySignedFieldsData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderFieldData

/-! # The fifty compiled carrier rank-datum fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

/-- One constructor for each identity-free field of a carrier rank datum, in
the fixed downstream scan layout. -/
inductive Field
  | keyRoute
  | keySegment
  | keyTranslateHorizontalPositive
  | keyTranslateHorizontalNegative
  | keyTranslateVerticalPositive
  | keyTranslateVerticalNegative
  | orderPositive
  | orderNegative
  | horizontal
  | normalizationHorizontalPositive
  | normalizationHorizontalNegative
  | normalizationVerticalPositive
  | normalizationVerticalNegative
  | boundaryPresence
  | crossingFirstRoute
  | crossingFirstSegment
  | crossingFirstStartHorizontalPositive
  | crossingFirstStartHorizontalNegative
  | crossingFirstStartVerticalPositive
  | crossingFirstStartVerticalNegative
  | crossingFirstFinishHorizontalPositive
  | crossingFirstFinishHorizontalNegative
  | crossingFirstFinishVerticalPositive
  | crossingFirstFinishVerticalNegative
  | crossingFirstTranslateHorizontalPositive
  | crossingFirstTranslateHorizontalNegative
  | crossingFirstTranslateVerticalPositive
  | crossingFirstTranslateVerticalNegative
  | crossingSecondRoute
  | crossingSecondSegment
  | crossingSecondStartHorizontalPositive
  | crossingSecondStartHorizontalNegative
  | crossingSecondStartVerticalPositive
  | crossingSecondStartVerticalNegative
  | crossingSecondFinishHorizontalPositive
  | crossingSecondFinishHorizontalNegative
  | crossingSecondFinishVerticalPositive
  | crossingSecondFinishVerticalNegative
  | crossingSecondTranslateHorizontalPositive
  | crossingSecondTranslateHorizontalNegative
  | crossingSecondTranslateVerticalPositive
  | crossingSecondTranslateVerticalNegative
  | crossingPointHorizontalPositive
  | crossingPointHorizontalNegative
  | crossingPointVerticalPositive
  | crossingPointVerticalNegative
  | ownershipHorizontalPositive
  | ownershipHorizontalNegative
  | ownershipVerticalPositive
  | ownershipVerticalNegative
  deriving DecidableEq, Fintype

/-- Zero-indexed position of a compiled field in the fixed rank scan. -/
def Field.index : Field → Nat
  | .keyRoute => 0
  | .keySegment => 1
  | .keyTranslateHorizontalPositive => 2
  | .keyTranslateHorizontalNegative => 3
  | .keyTranslateVerticalPositive => 4
  | .keyTranslateVerticalNegative => 5
  | .orderPositive => 6
  | .orderNegative => 7
  | .horizontal => 8
  | .normalizationHorizontalPositive => 9
  | .normalizationHorizontalNegative => 10
  | .normalizationVerticalPositive => 11
  | .normalizationVerticalNegative => 12
  | .boundaryPresence => 13
  | .crossingFirstRoute => 14
  | .crossingFirstSegment => 15
  | .crossingFirstStartHorizontalPositive => 16
  | .crossingFirstStartHorizontalNegative => 17
  | .crossingFirstStartVerticalPositive => 18
  | .crossingFirstStartVerticalNegative => 19
  | .crossingFirstFinishHorizontalPositive => 20
  | .crossingFirstFinishHorizontalNegative => 21
  | .crossingFirstFinishVerticalPositive => 22
  | .crossingFirstFinishVerticalNegative => 23
  | .crossingFirstTranslateHorizontalPositive => 24
  | .crossingFirstTranslateHorizontalNegative => 25
  | .crossingFirstTranslateVerticalPositive => 26
  | .crossingFirstTranslateVerticalNegative => 27
  | .crossingSecondRoute => 28
  | .crossingSecondSegment => 29
  | .crossingSecondStartHorizontalPositive => 30
  | .crossingSecondStartHorizontalNegative => 31
  | .crossingSecondStartVerticalPositive => 32
  | .crossingSecondStartVerticalNegative => 33
  | .crossingSecondFinishHorizontalPositive => 34
  | .crossingSecondFinishHorizontalNegative => 35
  | .crossingSecondFinishVerticalPositive => 36
  | .crossingSecondFinishVerticalNegative => 37
  | .crossingSecondTranslateHorizontalPositive => 38
  | .crossingSecondTranslateHorizontalNegative => 39
  | .crossingSecondTranslateVerticalPositive => 40
  | .crossingSecondTranslateVerticalNegative => 41
  | .crossingPointHorizontalPositive => 42
  | .crossingPointHorizontalNegative => 43
  | .crossingPointVerticalPositive => 44
  | .crossingPointVerticalNegative => 45
  | .ownershipHorizontalPositive => 46
  | .ownershipHorizontalNegative => 47
  | .ownershipVerticalPositive => 48
  | .ownershipVerticalNegative => 49

/-- The already-verified selected values emitted for one compiled field. -/
def Field.values (field : Field) : List RouteDescriptor → List Nat :=
  match field with
  | .keyRoute => CarrierRankKeyRouteField.values
  | .keySegment => CarrierRankKeySegmentField.values
  | .keyTranslateHorizontalPositive =>
      CarrierRankKeySignedFields.horizontalPositiveValues
  | .keyTranslateHorizontalNegative =>
      CarrierRankKeySignedFields.horizontalNegativeValues
  | .keyTranslateVerticalPositive =>
      CarrierRankKeySignedFields.verticalPositiveValues
  | .keyTranslateVerticalNegative =>
      CarrierRankKeySignedFields.verticalNegativeValues
  | .orderPositive => CarrierRankOrderField.values true
  | .orderNegative => CarrierRankOrderField.values false
  | .horizontal => CarrierRankHorizontalField.values
  | .normalizationHorizontalPositive =>
      CarrierNormalizationOffsetField.values .horizontalPositive
  | .normalizationHorizontalNegative =>
      CarrierNormalizationOffsetField.values .horizontalNegative
  | .normalizationVerticalPositive =>
      CarrierNormalizationOffsetField.values .verticalPositive
  | .normalizationVerticalNegative =>
      CarrierNormalizationOffsetField.values .verticalNegative
  | .boundaryPresence => CarrierBoundaryPresenceField.values
  | .crossingFirstRoute =>
      CarrierCrossingRecordSourceField.values .firstRoute
  | .crossingFirstSegment =>
      CarrierCrossingIndexedSegmentField.values .firstSegmentIndex
  | .crossingFirstStartHorizontalPositive =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .first .start true true)
  | .crossingFirstStartHorizontalNegative =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .first .start true false)
  | .crossingFirstStartVerticalPositive =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .first .start false true)
  | .crossingFirstStartVerticalNegative =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .first .start false false)
  | .crossingFirstFinishHorizontalPositive =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .first .finish true true)
  | .crossingFirstFinishHorizontalNegative =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .first .finish true false)
  | .crossingFirstFinishVerticalPositive =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .first .finish false true)
  | .crossingFirstFinishVerticalNegative =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .first .finish false false)
  | .crossingFirstTranslateHorizontalPositive =>
      CarrierCrossingRecordSourceField.values
        .firstTranslateHorizontalPositive
  | .crossingFirstTranslateHorizontalNegative =>
      CarrierCrossingRecordSourceField.values
        .firstTranslateHorizontalNegative
  | .crossingFirstTranslateVerticalPositive =>
      CarrierCrossingRecordSourceField.values .firstTranslateVerticalPositive
  | .crossingFirstTranslateVerticalNegative =>
      CarrierCrossingRecordSourceField.values .firstTranslateVerticalNegative
  | .crossingSecondRoute =>
      CarrierCrossingRecordSourceField.values .secondRoute
  | .crossingSecondSegment =>
      CarrierCrossingRecordSourceField.values .secondSegment
  | .crossingSecondStartHorizontalPositive =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .second .start true true)
  | .crossingSecondStartHorizontalNegative =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .second .start true false)
  | .crossingSecondStartVerticalPositive =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .second .start false true)
  | .crossingSecondStartVerticalNegative =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .second .start false false)
  | .crossingSecondFinishHorizontalPositive =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .second .finish true true)
  | .crossingSecondFinishHorizontalNegative =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .second .finish true false)
  | .crossingSecondFinishVerticalPositive =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .second .finish false true)
  | .crossingSecondFinishVerticalNegative =>
      CarrierCrossingIndexedSegmentField.values
        (.coordinate .second .finish false false)
  | .crossingSecondTranslateHorizontalPositive =>
      CarrierCrossingRecordSourceField.values
        .secondTranslateHorizontalPositive
  | .crossingSecondTranslateHorizontalNegative =>
      CarrierCrossingRecordSourceField.values
        .secondTranslateHorizontalNegative
  | .crossingSecondTranslateVerticalPositive =>
      CarrierCrossingRecordSourceField.values .secondTranslateVerticalPositive
  | .crossingSecondTranslateVerticalNegative =>
      CarrierCrossingRecordSourceField.values .secondTranslateVerticalNegative
  | .crossingPointHorizontalPositive =>
      CarrierCrossingPointField.values .horizontalPositive
  | .crossingPointHorizontalNegative =>
      CarrierCrossingPointField.values .horizontalNegative
  | .crossingPointVerticalPositive =>
      CarrierCrossingPointField.values .verticalPositive
  | .crossingPointVerticalNegative =>
      CarrierCrossingPointField.values .verticalNegative
  | .ownershipHorizontalPositive =>
      CarrierOwnershipShiftField.values .horizontalPositive
  | .ownershipHorizontalNegative =>
      CarrierOwnershipShiftField.values .horizontalNegative
  | .ownershipVerticalPositive =>
      CarrierOwnershipShiftField.values .verticalPositive
  | .ownershipVerticalNegative =>
      CarrierOwnershipShiftField.values .verticalNegative

/-- Scan fields zero through thirteen. -/
def prefixFields : List Field :=
  [.keyRoute,
    .keySegment,
    .keyTranslateHorizontalPositive,
    .keyTranslateHorizontalNegative,
    .keyTranslateVerticalPositive,
    .keyTranslateVerticalNegative,
    .orderPositive,
    .orderNegative,
    .horizontal,
    .normalizationHorizontalPositive,
    .normalizationHorizontalNegative,
    .normalizationVerticalPositive,
    .normalizationVerticalNegative,
    .boundaryPresence]

/-- Scan fields fourteen through twenty-seven. -/
def firstCrossingFields : List Field :=
  [.crossingFirstRoute,
    .crossingFirstSegment,
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
    .crossingFirstTranslateVerticalNegative]

/-- Scan fields twenty-eight through forty-one. -/
def secondCrossingFields : List Field :=
  [.crossingSecondRoute,
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
    .crossingSecondTranslateVerticalNegative]

/-- Scan fields forty-two through forty-nine. -/
def suffixFields : List Field :=
  [.crossingPointHorizontalPositive,
    .crossingPointHorizontalNegative,
    .crossingPointVerticalPositive,
    .crossingPointVerticalNegative,
    .ownershipHorizontalPositive,
    .ownershipHorizontalNegative,
    .ownershipVerticalPositive,
    .ownershipVerticalNegative]

/-- All compiled fields in their exact zero-through-forty-nine scan order. -/
def all : List Field :=
  prefixFields ++ firstCrossingFields ++ secondCrossingFields ++ suffixFields

@[simp] theorem all_indices : all.map Field.index = List.range 50 := by
  native_decide

/-- Selected-value columns for an arbitrary fixed compiled-field list. -/
def columnsFor (fields : List Field)
    (descriptors : List RouteDescriptor) : List (List Nat) :=
  fields.map fun field => field.values descriptors

def prefixColumns := columnsFor prefixFields

def firstCrossingColumns := columnsFor firstCrossingFields

def secondCrossingColumns := columnsFor secondCrossingFields

def suffixColumns := columnsFor suffixFields

/-- The fifty compiled selected-value columns. -/
def columns : List RouteDescriptor → List (List Nat) :=
  columnsFor all

@[simp] theorem columns_eq_groups (descriptors : List RouteDescriptor) :
    columns descriptors =
      prefixColumns descriptors ++
      firstCrossingColumns descriptors ++
      secondCrossingColumns descriptors ++
      suffixColumns descriptors := by
  simp [columns, columnsFor, prefixColumns, firstCrossingColumns,
    secondCrossingColumns, suffixColumns, all]

/-- Encode an arbitrary fixed field list consecutively in column-major order. -/
def encodedFields (fields : List Field)
    (descriptors : List RouteDescriptor) :
    List UnaryFieldEncoderMachine.Symbol :=
  fields.flatMap fun field =>
    UnaryFieldEncoderMachine.unaryFields (field.values descriptors)

def encodedPrefix := encodedFields prefixFields

def encodedFirstCrossing := encodedFields firstCrossingFields

def encodedSecondCrossing := encodedFields secondCrossingFields

def encodedSuffix := encodedFields suffixFields

/-- Unary column-major token stream consumed by the downstream rank scan. -/
def encodedColumns (descriptors : List RouteDescriptor) :
    List UnaryFieldEncoderMachine.Symbol :=
  encodedFields all descriptors

@[simp] theorem encodedColumns_eq_groups
    (descriptors : List RouteDescriptor) :
    encodedColumns descriptors =
      encodedPrefix descriptors ++
      encodedFirstCrossing descriptors ++
      encodedSecondCrossing descriptors ++
      encodedSuffix descriptors := by
  simp [encodedColumns, encodedFields, encodedPrefix,
    encodedFirstCrossing, encodedSecondCrossing, encodedSuffix, all]

@[simp] theorem encodedColumns_eq_flatMap_columns
    (descriptors : List RouteDescriptor) :
    encodedColumns descriptors =
      (columns descriptors).flatMap
        UnaryFieldEncoderMachine.unaryFields := by
  simp [encodedColumns, encodedFields, columns, columnsFor,
    List.flatMap_map]

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing
