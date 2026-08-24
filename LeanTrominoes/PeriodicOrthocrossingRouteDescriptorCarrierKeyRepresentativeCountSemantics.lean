/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeTrueCountSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRepresentativeOrderSemantics

/-! # Multiplicities in retained route-descriptor key order -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- Under exact support and active-value projection, true-counting the
selected padded rows lists every retained key's complete candidate
multiplicity in the same stable retained order. -/
theorem trueCounts_selectedPaddedCarrierKeyRows_eq
    (period : Nat) (descriptors : List RouteDescriptor)
    (correct :
      CorrectSupport
        (routeDescriptorTerminalCarrierKeys descriptors)
        (paddedCarrierKeyCandidateStream descriptors))
    (candidateValues :
      (paddedCarrierKeyCandidateStream descriptors).filterMap
          Candidate.value =
        routeDescriptorCarrierKeyCandidatesAtPeriod period descriptors) :
    DelimitedBinaryWordTrueCounts.counts
        (selectedRows (paddedCarrierKeyCandidateStream descriptors)) =
      (routeDescriptorRetainedCarrierKeysAtPeriod
        period descriptors).map fun key =>
          DelimitedBinaryWordTrueCounts.countTrue
            (LastRepresentativeEqualityRows.equalityRow
              (values (paddedCarrierKeyCandidateStream descriptors))
              (some key)) := by
  rw [trueCounts_selectedRows
    (routeDescriptorTerminalCarrierKeys descriptors)
    (paddedCarrierKeyCandidateStream descriptors) correct]
  let rowCount : Option CarrierKey → Nat := fun value =>
    DelimitedBinaryWordTrueCounts.countTrue
      (LastRepresentativeEqualityRows.equalityRow
        (values (paddedCarrierKeyCandidateStream descriptors)) value)
  change _ =
    (routeDescriptorRetainedCarrierKeysAtPeriod
      period descriptors).map fun key => rowCount (some key)
  have mapSome :
      (routeDescriptorRetainedCarrierKeysAtPeriod
          period descriptors).map (fun key => rowCount (some key)) =
        ((routeDescriptorRetainedCarrierKeysAtPeriod
          period descriptors).map some).map rowCount := by
    rw [List.map_map]
    rfl
  rw [mapSome]
  apply congrArg (List.map rowCount)
  rw [← paddedCarrierKeySelectedValues_eq_retainedKeys
    period descriptors candidateValues]
  apply List.filter_congr
  intro value _valueMember
  by_cases member : value ∈
      (routeDescriptorTerminalCarrierKeys descriptors).map some <;>
    simp [member]

end LeanTrominoes.PeriodicOrthocrossing
