/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldAlignmentSemantics

/-! # Semantics of all selected carrier-key fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyField

/-- Representative lookup returns the corresponding selected carrier rank
field for every physical-key selector and every period. -/
theorem values_eq_selectedFieldValuesAtPeriod
    (field : CarrierKeyFieldProjector.Field)
    (period : Nat) (descriptors : List RouteDescriptor) :
    values field descriptors =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        period descriptors (rankValue field) := by
  unfold values CarrierSourceKeyRepresentativeLookup.values
    CarrierRankDatumLookup.selectedFieldValuesAtPeriod
  rw [alignedValuesWithSentinel_eq_fieldValuesWithSentinelAtPeriod]

end CarrierRankKeyField
end LeanTrominoes.PeriodicOrthocrossing

end
