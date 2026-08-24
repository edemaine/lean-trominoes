/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisTaggedPairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyStreamData

/-! # Key-derived crossing axes of a descriptor stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

/-- Over any self-indexed descriptor stream with local route shapes, the
complete tagged-pair crossing-axis stream is the carrier-axis datum mapped
over the complete padded crossing candidate stream. -/
theorem crossingCarrierKeyAxisValues_stream_eq_map_candidates
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (localShapes : ∀ descriptor ∈ descriptors,
      ∃ shape : RouteShape, shape.Matches descriptor) :
    (taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors).flatMap (fun pair =>
      crossingCarrierKeyAxisValues (descriptorSlotPairTokens pair)) =
      (paddedCrossingCarrierKeyCandidateStream descriptors).map
        (RouteDescriptorCarrierKeyAxisDatum.value descriptors ∘
          Candidate.value) := by
  unfold paddedCrossingCarrierKeyCandidateStream
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro pair pairMember
  have pairMembers := List.mem_product.mp pairMember
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
  have firstMember := descriptorMember pair.1 pairMembers.1
  have secondMember := descriptorMember pair.2 pairMembers.2
  rcases localShapes pair.1.1 firstMember with
    ⟨firstShape, firstMatches⟩
  rcases localShapes pair.2.1 secondMember with
    ⟨secondShape, secondMatches⟩
  exact crossingCarrierKeyAxisValues_eq_map_candidates_of_matches
    descriptors selfIndexed firstShape secondShape pair
    firstMatches secondMatches firstMember secondMember

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
