/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRowsData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyPrefixSemantics

/-! # Semantics of retained route-descriptor carrier-key rows -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The retained equality rows are exactly the rows of the stable retained
carrier-key list, with columns aligned to the complete candidate stream. -/
theorem routeDescriptorRetainedCarrierKeyRowsAtPeriod_eq
    (period : Nat) (descriptors : List RouteDescriptor) :
    routeDescriptorRetainedCarrierKeyRowsAtPeriod period descriptors =
      ⟨(routeDescriptorRetainedCarrierKeysAtPeriod
          period descriptors).map
        (LastRepresentativeEqualityRows.equalityRow
          (routeDescriptorCarrierKeyCandidatesAtPeriod
            period descriptors))⟩ := by
  unfold routeDescriptorRetainedCarrierKeyRowsAtPeriod
    routeDescriptorCarrierKeyCandidatesAtPeriod
  rw [LastRepresentativeEqualityRows.prefixSupportedRows_equalityRows]
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
