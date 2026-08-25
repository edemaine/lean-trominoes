/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeySignedFieldsData

/-! # Signed carrier-key fields as rank-scan columns two through five -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeySignedFields

theorem horizontalPositiveValues_eq_fieldTwo
    (period : Nat) (descriptors : List RouteDescriptor) :
    horizontalPositiveValues descriptors =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        period descriptors
        (fun datum => datum.scanUnaryFields.getD 2 0) := by
  unfold horizontalPositiveValues
  simpa only [CarrierRankKeyField.index] using
    CarrierRankKeyField.values_eq_indexedField
      .horizontalPositive period descriptors

theorem horizontalNegativeValues_eq_fieldThree
    (period : Nat) (descriptors : List RouteDescriptor) :
    horizontalNegativeValues descriptors =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        period descriptors
        (fun datum => datum.scanUnaryFields.getD 3 0) := by
  unfold horizontalNegativeValues
  simpa only [CarrierRankKeyField.index] using
    CarrierRankKeyField.values_eq_indexedField
      .horizontalNegative period descriptors

theorem verticalPositiveValues_eq_fieldFour
    (period : Nat) (descriptors : List RouteDescriptor) :
    verticalPositiveValues descriptors =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        period descriptors
        (fun datum => datum.scanUnaryFields.getD 4 0) := by
  unfold verticalPositiveValues
  simpa only [CarrierRankKeyField.index] using
    CarrierRankKeyField.values_eq_indexedField
      .verticalPositive period descriptors

theorem verticalNegativeValues_eq_fieldFive
    (period : Nat) (descriptors : List RouteDescriptor) :
    verticalNegativeValues descriptors =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        period descriptors
        (fun datum => datum.scanUnaryFields.getD 5 0) := by
  unfold verticalNegativeValues
  simpa only [CarrierRankKeyField.index] using
    CarrierRankKeyField.values_eq_indexedField
      .verticalNegative period descriptors

end CarrierRankKeySignedFields
end LeanTrominoes.PeriodicOrthocrossing

end
