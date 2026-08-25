/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumUnaryData

/-! # Rank-scan indices of source-key crossing-record fields -/

namespace LeanTrominoes.PeriodicOrthocrossing

open CarrierCrossingRecordSourceField

/-- Every source-key crossing-record projector names its exact fixed column
in the fifty-field carrier rank scan. -/
@[simp] theorem CarrierNodeRankDatum.scanUnaryFields_getD_sourceField
    (field : Field) (datum : CarrierNodeRankDatum) :
    datum.scanUnaryFields.getD (index field) 0 = rankValue field datum := by
  cases crossingEq : datum.boundaryCrossing with
  | none =>
      cases field <;>
        simp [CarrierNodeRankDatum.scanUnaryFields,
          CarrierNodeRankDatum.scanDatum, CarrierRankScanDatum.unaryFields,
          carrierKeyUnaryFields, cellUnaryFields, signedUnaryFields,
          optionalCrossingRecordCodeUnaryFields, index, rankValue,
          crossingEq]
  | some record =>
      rcases record with
        ⟨⟨firstRoute, firstSegment, firstStart, firstFinish⟩,
          firstTranslate,
          ⟨secondRoute, secondSegment, secondStart, secondFinish⟩,
          secondTranslate, point⟩
      cases field <;>
        simp [CarrierNodeRankDatum.scanUnaryFields,
          CarrierNodeRankDatum.scanDatum, CarrierRankScanDatum.unaryFields,
          carrierKeyUnaryFields, cellUnaryFields, signedUnaryFields,
          optionalCrossingRecordCodeUnaryFields,
          IndexedGridSegmentCode.scanUnaryFields,
          CrossingRecordCode.scanUnaryFields, index, rankValue,
          component, keyField, recordKey,
          CarrierKeyFieldProjector.keyValue, crossingEq]

namespace CarrierCrossingRecordSourceField

/-- Each compiled family member is precisely the selected rank-scan column
named by `index`. -/
theorem values_eq_indexedField
    (field : Field) (period : Nat)
    (descriptors : List RouteDescriptor) :
    values field descriptors =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        period descriptors
        (fun datum => datum.scanUnaryFields.getD (index field) 0) := by
  rw [values_eq_selectedFieldValuesAtPeriod]
  congr 1
  funext datum
  exact (datum.scanUnaryFields_getD_sourceField field).symm

end CarrierCrossingRecordSourceField
end LeanTrominoes.PeriodicOrthocrossing
