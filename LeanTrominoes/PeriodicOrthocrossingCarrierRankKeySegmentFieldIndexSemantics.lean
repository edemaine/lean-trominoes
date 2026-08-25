/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeySegmentFieldData

/-! # Selected carrier-key segment field as rank-scan column one -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeySegmentField

/-- At every period, the compiled segment-index lookup is precisely selected
rank-scan column one. -/
theorem values_eq_fieldOne
    (period : Nat) (descriptors : List RouteDescriptor) :
    values descriptors =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        period descriptors
        (fun datum => datum.scanUnaryFields.getD 1 0) := by
  unfold values
  simpa only [CarrierRankKeyField.index] using
    CarrierRankKeyField.values_eq_indexedField
      .segment period descriptors

end CarrierRankKeySegmentField
end LeanTrominoes.PeriodicOrthocrossing

end
