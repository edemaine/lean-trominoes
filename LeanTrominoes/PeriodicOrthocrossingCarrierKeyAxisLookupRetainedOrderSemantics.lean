/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisLookupSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRepresentativeOrderSemantics

/-! # Retained-key order of carrier-axis lookup -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisLookup

open PaddedSupportedLastRepresentativeEqualityRows

/-- Key-derived lookup values occur in the exact retained carrier-key order. -/
theorem values_eq_retainedKeys_map
    (period : Nat) (descriptors : List RouteDescriptor)
    (rowsEq :
      paddedCarrierKeyRepresentativeRows descriptors =
        selectedRows (paddedCarrierKeyCandidateStream descriptors))
    (correct :
      CorrectSupport
        (routeDescriptorTerminalCarrierKeys descriptors)
        (paddedCarrierKeyCandidateStream descriptors))
    (candidateValues :
      (paddedCarrierKeyCandidateStream descriptors).filterMap
          Candidate.value =
        routeDescriptorCarrierKeyCandidatesAtPeriod period descriptors)
    (datum : Option CarrierKey → Nat)
    (axisValues :
      CarrierKeyAxisStream.values descriptors =
        (PaddedSupportedLastRepresentativeEqualityRows.values
          (paddedCarrierKeyCandidateStream descriptors)).map datum) :
    values descriptors =
      (routeDescriptorRetainedCarrierKeysAtPeriod period descriptors).map
        fun key => datum (some key) := by
  rw [values_eq_selectedValues_map descriptors
    (routeDescriptorTerminalCarrierKeys descriptors)
    rowsEq correct datum axisValues]
  have mapSome :
      (routeDescriptorRetainedCarrierKeysAtPeriod
          period descriptors).map (fun key => datum (some key)) =
        ((routeDescriptorRetainedCarrierKeysAtPeriod
          period descriptors).map some).map datum := by
    rw [List.map_map]
    rfl
  rw [mapSome]
  apply congrArg (List.map datum)
  rw [← paddedCarrierKeySelectedValues_eq_retainedKeys
    period descriptors candidateValues]

end CarrierKeyAxisLookup
end LeanTrominoes.PeriodicOrthocrossing
