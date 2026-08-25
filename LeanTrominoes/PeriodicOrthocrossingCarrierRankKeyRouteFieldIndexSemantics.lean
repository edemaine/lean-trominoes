/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumKeyRouteFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyRouteFieldSemantics

/-! # Selected carrier-key route field as rank-scan column zero -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyRouteField

/-- At every period, the compiled route-index lookup is precisely selected
rank-scan column zero. -/
theorem values_eq_fieldZero
    (period : Nat) (descriptors : List RouteDescriptor) :
    values descriptors =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        period descriptors
        (fun datum => datum.scanUnaryFields.getD 0 0) := by
  simpa only [CarrierNodeRankDatum.scanUnaryFields_getD_zero] using
    values_eq_selectedFieldValuesAtPeriod period descriptors

end CarrierRankKeyRouteField
end LeanTrominoes.PeriodicOrthocrossing

end
