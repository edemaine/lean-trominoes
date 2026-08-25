/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumUnaryData
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftFieldNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumLookupNumericSemantics

/-! # Rank-scan indices of carrier ownership-shift fields -/

namespace LeanTrominoes.PeriodicOrthocrossing

open CarrierOwnershipShiftField

/-- Each ownership-shift projector names its exact fixed column in the
fifty-field carrier rank scan. -/
@[simp] theorem CarrierNodeRankDatum.scanUnaryFields_getD_ownershipShiftField
    (field : Field) (datum : CarrierNodeRankDatum) :
    datum.scanUnaryFields.getD (index field) 0 = rankValue field datum := by
  cases crossingEq : datum.boundaryCrossing with
  | none =>
      cases field <;>
        simp [CarrierNodeRankDatum.scanUnaryFields,
          CarrierNodeRankDatum.scanDatum, CarrierRankScanDatum.unaryFields,
          carrierKeyUnaryFields, cellUnaryFields, signedUnaryFields,
          optionalCrossingRecordCodeUnaryFields, index, rankValue,
          shiftValue, CarrierOwnershipShiftField.horizontal,
          CarrierOwnershipShiftField.keepPositive, crossingEq]
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
          shiftValue, CarrierOwnershipShiftField.horizontal,
          CarrierOwnershipShiftField.keepPositive, crossingEq]

namespace CarrierOwnershipShiftField

/-- Every compiled ownership-shift family member is the selected rank-scan
column named by `index`. -/
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
  exact (datum.scanUnaryFields_getD_ownershipShiftField field).symm

end CarrierOwnershipShiftField
end LeanTrominoes.PeriodicOrthocrossing
