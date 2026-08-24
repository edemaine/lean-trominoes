/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListOptionSupportedDedup
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyPrefixSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRowsData

/-! # Retained key order of padded route-descriptor candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- Once inactive padded slots project to the compact carrier candidate
stream, stable support-aware selection has exactly the compact retained-key
order, with `some` reattached. -/
theorem paddedCarrierKeySelectedValues_eq_retainedKeys
    (period : Nat) (descriptors : List RouteDescriptor)
    (candidateValues :
      (paddedCarrierKeyCandidateStream descriptors).filterMap
          Candidate.value =
        routeDescriptorCarrierKeyCandidatesAtPeriod period descriptors) :
    ((values (paddedCarrierKeyCandidateStream descriptors)).dedup.filter
        fun value => value ∈
          (routeDescriptorTerminalCarrierKeys descriptors).map some) =
      (routeDescriptorRetainedCarrierKeysAtPeriod
        period descriptors).map some := by
  rw [List.dedup_filter_mem_map_some_eq]
  have presentValues :
      (values (paddedCarrierKeyCandidateStream descriptors)).filterMap id =
        (paddedCarrierKeyCandidateStream descriptors).filterMap
          Candidate.value := by
    unfold values
    rw [List.filterMap_map]
    rfl
  rw [presentValues, candidateValues]
  congr 1
  unfold routeDescriptorRetainedCarrierKeysAtPeriod
    routeDescriptorCarrierKeyCandidatesAtPeriod
  rw [retainedCarrierKeysOfOccurrencesAndPairs_eq_terminalPrefixFilter]
  unfold routeDescriptorTerminalCarrierKeys
  apply List.filter_congr
  intro key _keyMember
  by_cases member :
      key ∈ occurrenceTerminalCarrierKeys
        (routeDescriptorNeighborOccurrences descriptors) <;>
    simp [member]

end LeanTrominoes.PeriodicOrthocrossing
