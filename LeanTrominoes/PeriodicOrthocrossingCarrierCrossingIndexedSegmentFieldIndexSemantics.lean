/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentFieldNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumUnaryData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumLookupNumericSemantics

/-! # Rank-scan indices of indexed crossing-segment fields -/

namespace LeanTrominoes.PeriodicOrthocrossing

open CarrierCrossingIndexedSegmentField

/-- Each indexed crossing-segment projector names its exact fixed column in
the fifty-field carrier rank scan. -/
@[simp] theorem CarrierNodeRankDatum.scanUnaryFields_getD_crossingIndexedSegmentField
    (field : Field) (datum : CarrierNodeRankDatum) :
    datum.scanUnaryFields.getD (index field) 0 = rankValue field datum := by
  cases crossingEq : datum.boundaryCrossing with
  | none =>
      cases field with
      | firstSegmentIndex =>
          simp [CarrierNodeRankDatum.scanUnaryFields,
            CarrierNodeRankDatum.scanDatum, CarrierRankScanDatum.unaryFields,
            carrierKeyUnaryFields, cellUnaryFields, signedUnaryFields,
            optionalCrossingRecordCodeUnaryFields, index, rankValue,
            crossingEq]
      | coordinate side endpoint horizontal keep =>
          cases side <;> cases endpoint <;>
            cases horizontal <;> cases keep <;>
              simp [CarrierNodeRankDatum.scanUnaryFields,
                CarrierNodeRankDatum.scanDatum,
                CarrierRankScanDatum.unaryFields,
                carrierKeyUnaryFields, cellUnaryFields, signedUnaryFields,
                optionalCrossingRecordCodeUnaryFields, index,
                coordinateBase, coordinateOffset, rankValue, crossingEq]
  | some record =>
      rcases record with
        ⟨⟨firstRoute, firstSegment, firstStart, firstFinish⟩,
          firstTranslate,
          ⟨secondRoute, secondSegment, secondStart, secondFinish⟩,
          secondTranslate, point⟩
      cases field with
      | firstSegmentIndex =>
          simp [CarrierNodeRankDatum.scanUnaryFields,
            CarrierNodeRankDatum.scanDatum, CarrierRankScanDatum.unaryFields,
            carrierKeyUnaryFields, cellUnaryFields, signedUnaryFields,
            optionalCrossingRecordCodeUnaryFields,
            IndexedGridSegmentCode.scanUnaryFields,
            CrossingRecordCode.scanUnaryFields, index, rankValue,
            recordValue, crossingEq]
      | coordinate side endpoint horizontal keep =>
          cases side <;> cases endpoint <;>
            cases horizontal <;> cases keep <;>
              simp [CarrierNodeRankDatum.scanUnaryFields,
                CarrierNodeRankDatum.scanDatum,
                CarrierRankScanDatum.unaryFields,
                carrierKeyUnaryFields, cellUnaryFields, signedUnaryFields,
                optionalCrossingRecordCodeUnaryFields,
                IndexedGridSegmentCode.scanUnaryFields,
                CrossingRecordCode.scanUnaryFields, index,
                coordinateBase, coordinateOffset, rankValue, recordValue,
                recordSegment, segmentEndpoint, coordinateValue, crossingEq]

namespace CarrierCrossingIndexedSegmentField

/-- Every compiled family member is the selected rank-scan column named by
`index`. -/
theorem values_numericRouteDescriptors_eq_indexedField
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ [])
    (field : Field) :
    values field (PeriodicCNF.numericRouteDescriptors formula) =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)
        (fun datum => datum.scanUnaryFields.getD (index field) 0) := by
  rw [values_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty field]
  rw [CarrierRankDatumLookup.selectedFieldValuesAtPeriod_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  congr 1
  funext datum
  exact
    (datum.scanUnaryFields_getD_crossingIndexedSegmentField field).symm

end CarrierCrossingIndexedSegmentField
end LeanTrominoes.PeriodicOrthocrossing
