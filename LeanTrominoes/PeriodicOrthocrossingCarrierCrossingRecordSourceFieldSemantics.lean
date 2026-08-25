/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldAlignmentSemantics

/-! # Selected source-key crossing-record field semantics -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingRecordSourceField

theorem values_eq_selectedFieldValuesAtPeriod
    (field : Field) (period : Nat)
    (descriptors : List RouteDescriptor) :
    values field descriptors =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        period descriptors (rankValue field) := by
  unfold values CarrierSourceKeyRepresentativeLookup.values
    CarrierRankDatumLookup.selectedFieldValuesAtPeriod
  rw [alignedValuesWithSentinel_eq_fieldValuesWithSentinelAtPeriod]

end CarrierCrossingRecordSourceField
end LeanTrominoes.PeriodicOrthocrossing

end
