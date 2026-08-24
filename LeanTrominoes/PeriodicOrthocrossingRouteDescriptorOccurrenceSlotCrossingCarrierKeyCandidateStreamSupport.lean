/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyCandidateSupport
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyStreamData

/-! # Support of slot-major crossing candidate streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorPairAffine

/-- For a self-indexed descriptor stream whose descriptors all have local
route shapes, the complete padded crossing scan is supported exactly by the
global terminal carrier-key stream. -/
theorem paddedCrossingCarrierKeyCandidateStream_correctSupport
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (localShapes : ∀ descriptor ∈ descriptors,
      ∃ shape : RouteShape, shape.Matches descriptor) :
    CorrectSupport
      (occurrenceTerminalCarrierKeys
        (routeDescriptorNeighborOccurrences descriptors))
      (paddedCrossingCarrierKeyCandidateStream descriptors) := by
  have descriptorMember : ∀ tagged ∈ taggedDescriptors descriptors,
      tagged.1 ∈ descriptors := by
    intro tagged taggedMember
    unfold taggedDescriptors at taggedMember
    rcases List.mem_flatMap.mp taggedMember with
      ⟨descriptor, descriptorMember, taggedMember⟩
    rcases List.mem_map.mp taggedMember with
      ⟨slot, _slotMember, taggedEq⟩
    subst tagged
    exact descriptorMember
  intro candidate candidateMember
  unfold paddedCrossingCarrierKeyCandidateStream at candidateMember
  rw [List.mem_flatMap] at candidateMember
  rcases candidateMember with ⟨pair, pairMember, candidateMember⟩
  have pairMembers := List.mem_product.mp pairMember
  have firstDescriptorMember := descriptorMember pair.1 pairMembers.1
  have secondDescriptorMember := descriptorMember pair.2 pairMembers.2
  rcases localShapes pair.1.1 firstDescriptorMember with
    ⟨firstShape, firstMatches⟩
  rcases localShapes pair.2.1 secondDescriptorMember with
    ⟨secondShape, secondMatches⟩
  exact paddedCrossingCarrierKeyCandidates_correctSupport_of_matches
    descriptors selfIndexed firstShape secondShape pair
    firstMatches secondMatches firstDescriptorMember
    secondDescriptorMember candidate candidateMember

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
