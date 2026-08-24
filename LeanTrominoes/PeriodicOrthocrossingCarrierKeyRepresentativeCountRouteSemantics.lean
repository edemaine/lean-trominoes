/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRepresentativeCountSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRepresentativeRowSemantics

/-! # Retained carrier-key counts under route invariants -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairAffine

/-- The standard route-stream invariants discharge the internal support and
representative-row contracts of the compiled count semantics. -/
theorem paddedCarrierKeyRepresentativeCounts_eq_of_routeInvariants
    (period : Nat) (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (localShapes : ∀ descriptor ∈ descriptors,
      ∃ shape : RouteShape, shape.Matches descriptor)
    (terminalValues :
      (paddedTerminalCarrierKeyCandidateStream descriptors).filterMap
          Candidate.value =
        occurrenceTerminalCarrierKeys
          (routeDescriptorNeighborOccurrences descriptors))
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
  apply paddedCarrierKeyRepresentativeCounts_eq
    period descriptors
  · exact paddedCarrierKeyRepresentativeRows_eq_selectedRows
      descriptors selfIndexed localShapes terminalValues
  · exact paddedCarrierKeyCandidateStream_correctSupport
      descriptors selfIndexed localShapes terminalValues
  · exact candidateValues

end LeanTrominoes.PeriodicOrthocrossing
