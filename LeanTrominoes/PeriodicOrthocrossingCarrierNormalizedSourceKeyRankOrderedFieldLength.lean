/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRepresentativeFieldLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRankOrderedFieldLength

/-! # Length alignment for normalized carrier source-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRankOrderedFields

theorem selectedFieldsAtPeriod_length
    (period : Nat) (descriptors : List RouteDescriptor) :
    (CarrierNormalizedSourceKeyRepresentativeFieldLookup.selectedFieldsAtPeriod
        period descriptors).length =
      (CarrierRankGlobal.ranks descriptors).length *
        CarrierSourceKeyRepresentativeFieldLookup.fieldCount := by
  unfold CarrierNormalizedSourceKeyRepresentativeFieldLookup.selectedFieldsAtPeriod
    LastTrueUnaryValueLookupMachine.lookups
    CarrierNormalizedSourceKeyRepresentativeFieldLookup.expandedRows
  rw [List.length_map]
  have physical :=
    CarrierSourceKeyRankOrderedFields.selectedFields_length descriptors
  unfold CarrierSourceKeyRepresentativeFieldLookup.selectedFields
    LastTrueUnaryValueLookupMachine.lookups at physical
  rw [List.length_map] at physical
  exact physical

end CarrierNormalizedSourceKeyRankOrderedFields
end LeanTrominoes.PeriodicOrthocrossing
