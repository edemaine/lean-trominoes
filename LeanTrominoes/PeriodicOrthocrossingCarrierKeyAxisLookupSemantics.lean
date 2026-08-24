/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeLookupSentinelSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisLookupData

/-! # Semantics of retained carrier-key axis lookup -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisLookup

open PaddedSupportedLastRepresentativeEqualityRows

/-- Once the padded values are a function of their optional carrier key, the
lookup returns that function in stable support-selected order. -/
theorem values_eq_selectedValues_map
    (descriptors : List RouteDescriptor) (base : List CarrierKey)
    (rowsEq :
      paddedCarrierKeyRepresentativeRows descriptors =
        selectedRows (paddedCarrierKeyCandidateStream descriptors))
    (correct :
      CorrectSupport
        base
        (paddedCarrierKeyCandidateStream descriptors))
    (datum : Option CarrierKey → Nat)
    (axisValues :
      CarrierKeyAxisStream.values descriptors =
        (PaddedSupportedLastRepresentativeEqualityRows.values
          (paddedCarrierKeyCandidateStream descriptors)).map datum) :
    values descriptors =
      (((PaddedSupportedLastRepresentativeEqualityRows.values
          (paddedCarrierKeyCandidateStream descriptors)).dedup.filter
        fun value => value ∈
          base.map some).map
            datum) := by
  unfold values
  rw [rowsEq]
  unfold CarrierKeyAxisStream.valuesWithSentinel
  rw [axisValues]
  rw [lookups_selectedRows_map_append_value
    base
    (paddedCarrierKeyCandidateStream descriptors) correct datum 0]
  apply congrArg (List.map datum)
  apply List.filter_congr
  intro value _valueMember
  by_cases member : value ∈ base.map some <;>
    simp [member]

end CarrierKeyAxisLookup
end LeanTrominoes.PeriodicOrthocrossing
