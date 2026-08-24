/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockSupport
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyActiveTemplateSupport
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyData

/-! # Support of one slot-major crossing candidate family -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorPairAffine

/-- The padded crossing candidates of two selected descriptor slots carry
exact support relative to the global terminal carrier-key stream. -/
theorem paddedCrossingCarrierKeyCandidates_correctSupport_of_matches
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (firstShape secondShape : RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : firstShape.Matches pair.1.1)
    (secondMatches : secondShape.Matches pair.2.1)
    (firstDescriptorMember : pair.1.1 ∈ descriptors)
    (secondDescriptorMember : pair.2.1 ∈ descriptors) :
    CorrectSupport
      (occurrenceTerminalCarrierKeys
        (routeDescriptorNeighborOccurrences descriptors))
      (paddedCrossingCarrierKeyCandidates pair) := by
  unfold paddedCrossingCarrierKeyCandidates
  apply correctSupport_candidates_of_active
  exact crossingCarrierKeyTemplateBlocks_correctActive_of_matches
    descriptors selfIndexed firstShape secondShape pair
    firstMatches secondMatches firstDescriptorMember
    secondDescriptorMember

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
