/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceAlignmentSemantics

/-! # Selected boundary-presence field semantics -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresenceField

/-- The compiled source-key lookup is exactly the boundary-presence field
of every selected carrier rank datum. -/
theorem values_eq_selectedFieldValuesAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    values descriptors =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        period descriptors rankValue := by
  unfold values CarrierSourceKeyRepresentativeLookup.values
    CarrierRankDatumLookup.selectedFieldValuesAtPeriod
  rw [alignedValuesWithSentinel_eq_fieldValuesWithSentinelAtPeriod]

end CarrierBoundaryPresenceField
end LeanTrominoes.PeriodicOrthocrossing

end
