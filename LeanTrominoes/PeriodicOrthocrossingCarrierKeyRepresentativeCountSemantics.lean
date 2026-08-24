/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRepresentativeCountData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRepresentativeCountSemantics

/-! # Semantics of compiled retained carrier-key counts -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- Any verified representative-row and candidate projection identifies the
compiled unary counts with per-key multiplicities in exact retained order. -/
theorem paddedCarrierKeyRepresentativeCounts_eq
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
        routeDescriptorCarrierKeyCandidatesAtPeriod period descriptors) :
    paddedCarrierKeyRepresentativeCounts descriptors =
      (routeDescriptorRetainedCarrierKeysAtPeriod
        period descriptors).map fun key =>
          DelimitedBinaryWordTrueCounts.countTrue
            (LastRepresentativeEqualityRows.equalityRow
              (values (paddedCarrierKeyCandidateStream descriptors))
              (some key)) := by
  unfold paddedCarrierKeyRepresentativeCounts
  rw [rowsEq]
  exact trueCounts_selectedPaddedCarrierKeyRows_eq
    period descriptors correct candidateValues

end LeanTrominoes.PeriodicOrthocrossing
