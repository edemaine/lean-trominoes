/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFilterMapFlatMap
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodePairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlotCrossingFilterSemantics

/-! # Semantics of slot-major crossing carrier-node streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

private theorem descriptor_mem_of_taggedDescriptors_mem
    {descriptors : List RouteDescriptor} {tagged : TaggedDescriptor}
    (taggedMember : tagged ∈ taggedDescriptors descriptors) :
    tagged.1 ∈ descriptors := by
  unfold taggedDescriptors at taggedMember
  rcases List.mem_flatMap.mp taggedMember with
    ⟨descriptor, descriptorMember, taggedMember⟩
  rcases List.mem_map.mp taggedMember with
    ⟨slot, _slotMember, taggedEq⟩
  subst tagged
  exact descriptorMember

/-- Under the numeric route-stream invariants, the compact slot-major
crossing-node stream is exactly the retained crossing-record boundary scan. -/
theorem crossingCarrierNodeActiveValueStream_eq_retainedBoundaryScan
    (period : Nat) (descriptors : List RouteDescriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors)
    (commonPeriod :
      ∀ descriptor ∈ descriptors, descriptor.gridSize = period)
    (localShapes :
      ∀ descriptor ∈ descriptors,
        RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape
          descriptor) :
    ((taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors).flatMap fun pair =>
      activeValues
        (crossingActivations (descriptorSlotPairTokens pair))
        (crossingCarrierNodeTemplateBlocks
          (pair.1.1, pair.2.1))) =
      (occurrencePairRetainedCrossingRecordScanAtPeriod period
        (routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
          period descriptors)).flatMap
            crossingRecordCarrierBoundaryNodes := by
  let taggedPairs := taggedDescriptors descriptors ×ˢ
    taggedDescriptors descriptors
  calc
    taggedPairs.flatMap (fun pair =>
        activeValues
          (crossingActivations (descriptorSlotPairTokens pair))
          (crossingCarrierNodeTemplateBlocks
            (pair.1.1, pair.2.1))) =
      taggedPairs.flatMap (fun pair =>
        (List.optionalFilteredPair
          (canonicalOrientedOccurrencePairAtPeriod period)
          (occurrenceAtSlot pair.1)
          (occurrenceAtSlot pair.2)).toList.flatMap
            (fun occurrencePair =>
              (occurrencePairRetainedCrossingRecordBlockAtPeriod
                period occurrencePair).flatMap
                  crossingRecordCarrierBoundaryNodes)) := by
        apply List.flatMap_congr
        intro pair pairMember
        have pairMembers := List.mem_product.mp pairMember
        have firstMember := descriptor_mem_of_taggedDescriptors_mem
          pairMembers.1
        have secondMember := descriptor_mem_of_taggedDescriptors_mem
          pairMembers.2
        rcases localShapes pair.1.1 firstMember with
          ⟨firstShape, firstMatches⟩
        rcases localShapes pair.2.1 secondMember with
          ⟨secondShape, secondMatches⟩
        rw [crossingCarrierNodeActiveValues_eq_optionalFilteredPair_of_matches
          firstShape secondShape pair firstMatches secondMatches]
        rw [commonPeriod pair.1.1 firstMember]
    _ = (taggedPairs.filterMap (fun pair =>
          List.optionalFilteredPair
            (canonicalOrientedOccurrencePairAtPeriod period)
            (occurrenceAtSlot pair.1)
            (occurrenceAtSlot pair.2))).flatMap
          (fun occurrencePair =>
            (occurrencePairRetainedCrossingRecordBlockAtPeriod
              period occurrencePair).flatMap
                crossingRecordCarrierBoundaryNodes) :=
      List.flatMap_toList_flatMap_eq_filterMap_flatMap
        taggedPairs
        (fun pair => List.optionalFilteredPair
          (canonicalOrientedOccurrencePairAtPeriod period)
          (occurrenceAtSlot pair.1)
          (occurrenceAtSlot pair.2))
        (fun occurrencePair =>
          (occurrencePairRetainedCrossingRecordBlockAtPeriod
            period occurrencePair).flatMap
              crossingRecordCarrierBoundaryNodes)
    _ = _ := by
      rw [filterMap_taggedDescriptorPairs_eq_crossings
        period descriptors selfIndexed]
      unfold occurrencePairRetainedCrossingRecordScanAtPeriod
      rw [List.flatMap_assoc]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
