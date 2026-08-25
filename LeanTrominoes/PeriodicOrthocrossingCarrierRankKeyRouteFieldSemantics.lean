/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyRouteFieldAlignmentSemantics

/-! # Semantics of the selected carrier-key route field -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyRouteField

/-- At every period, compact representative lookup returns exactly the
selected route-index field of the carrier rank data. -/
theorem values_eq_selectedFieldValuesAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    values descriptors =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        period descriptors (fun datum => datum.key.1) := by
  unfold values CarrierSourceKeyRepresentativeLookup.values
    CarrierRankDatumLookup.selectedFieldValuesAtPeriod
  rw [alignedValuesWithSentinel_eq_fieldValuesWithSentinelAtPeriod]

end CarrierRankKeyRouteField
end LeanTrominoes.PeriodicOrthocrossing

end
