/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRowsData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyPrefixSemantics
import LeanTrominoes.SupportedLastRepresentativeEqualityRowsSemantics

/-! # Semantics of retained route-descriptor carrier-key rows -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The retained guarded equality rows are exactly the rows of the stable
retained carrier-key list, with columns aligned to the complete candidate
stream and a final false support guard. -/
theorem routeDescriptorRetainedCarrierKeyRowsAtPeriod_eq
    (period : Nat) (descriptors : List RouteDescriptor) :
    routeDescriptorRetainedCarrierKeyRowsAtPeriod period descriptors =
      ⟨(routeDescriptorRetainedCarrierKeysAtPeriod
          period descriptors).map
        (SupportedLastRepresentativeEqualityRows.row
          (routeDescriptorTerminalCarrierKeys descriptors)
          (routeDescriptorCarrierKeyCandidatesAtPeriod
            period descriptors))⟩ := by
  unfold routeDescriptorRetainedCarrierKeyRowsAtPeriod
  rw [SupportedLastRepresentativeEqualityRows.selectedRows_eq]
  congr 1
  unfold routeDescriptorRetainedCarrierKeysAtPeriod
    routeDescriptorTerminalCarrierKeys
  rw [retainedCarrierKeysOfOccurrencesAndPairs_eq_terminalPrefixFilter]
  congr 1
  apply List.filter_congr
  intro key _keyMember
  by_cases member :
      key ∈ occurrenceTerminalCarrierKeys
        (routeDescriptorNeighborOccurrences descriptors) <;>
    simp [member]

end LeanTrominoes.PeriodicOrthocrossing
