/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftEmitterSemantics
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftCandidateOccurrenceSemantics
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlotActiveNeighborSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairBlockMapSemantics
import LeanTrominoes.ListFilterMapFlatMap
import LeanTrominoes.ListOptionalFilteredProduct

/-! # Semantics of common-shift canonical-left source-key streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyStream

open RouteDescriptorOccurrenceSlotBinaryWords
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

theorem guardedWords_eq_candidates
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    guardedWords pairs =
      (candidates pairs).map
        (PaddedSupportedCandidateWords.guardedWord
          CarrierNodeSourceKeys.word) := by
  unfold guardedWords candidates
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      simp [induction]

/-- Mapping the common-shift inner compiler over canonical pair blocks emits
exactly the encoding of their concatenated guarded candidate words. -/
@[simp] theorem emittedStream_encodeDescriptorSlotPairs
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    emittedStream
        (RouteDescriptorOccurrenceSlotPairFieldTags.encodeDescriptorSlotPairs
          pairs) =
      DelimitedBinaryWords.encode ⟨guardedWords pairs⟩ := by
  unfold emittedStream
  rw [RouteDescriptorOccurrenceSlotPairFieldTags.mappedOutput_encodeDescriptorSlotPairs]
  simp only [CanonicalCrossingShiftLeftSourceKeyEmitter.emittedTokens_eq_candidates]
  unfold guardedWords DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]

/-- Removing inactive padding from the complete tagged-pair stream gives
exactly the physical occurrence-pair common-shift scan. -/
theorem filterMap_candidates_eq_occurrencePairShiftScan
    (period : Nat) (descriptors : List RouteDescriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors)
    (commonPeriod :
      ∀ descriptor ∈ descriptors, descriptor.gridSize = period)
    (localShapes :
      ∀ descriptor ∈ descriptors,
        RouteDescriptor.HasLocalShape descriptor) :
    (candidates
        (taggedDescriptors descriptors ×ˢ
          taggedDescriptors descriptors)).filterMap
        PaddedSupportedLastRepresentativeEqualityRows.Candidate.value =
      occurrencePairCanonicalLeftSourceKeyShiftScanAtPeriod period
        (routeDescriptorNeighborOccurrences descriptors) := by
  let taggedPairs := taggedDescriptors descriptors ×ˢ
    taggedDescriptors descriptors
  unfold candidates
  rw [List.filterMap_eq_flatMap_toList, List.flatMap_assoc]
  calc
    taggedPairs.flatMap (fun pair =>
        (RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyCandidates
          pair).flatMap fun candidate => candidate.value.toList) =
      taggedPairs.flatMap (fun pair =>
        match occurrenceAtSlot pair.1, occurrenceAtSlot pair.2 with
        | some first, some second =>
            occurrencePairCanonicalLeftSourceKeyShiftBlockAtPeriod
              period (first, second)
        | _, _ => []) := by
          apply List.flatMap_congr
          intro pair pairMember
          have pairMembers := List.mem_product.mp pairMember
          have firstMember :=
            descriptor_mem_of_taggedDescriptors_mem pairMembers.1
          have secondMember :=
            descriptor_mem_of_taggedDescriptors_mem pairMembers.2
          rcases localShapes pair.1.1 firstMember with
            ⟨firstShape, firstMatches⟩
          rcases localShapes pair.2.1 secondMember with
            ⟨secondShape, secondMatches⟩
          rw [← List.filterMap_eq_flatMap_toList]
          rw [
            RouteDescriptorOccurrenceSlotCrossing.filterMap_canonicalCrossingShiftLeftSourceKeyCandidates_eq_occurrenceBlock_of_matches
              firstShape secondShape pair firstMatches secondMatches]
          rw [commonPeriod pair.1.1 firstMember]
          rfl
    _ = taggedPairs.flatMap (fun pair =>
        (List.optionalFilteredPair
          (fun _ : (IndexedGridSegment × Cell) ×
            (IndexedGridSegment × Cell) => true)
          (occurrenceAtSlot pair.1) (occurrenceAtSlot pair.2)).toList.flatMap
            (occurrencePairCanonicalLeftSourceKeyShiftBlockAtPeriod
              period)) := by
          apply List.flatMap_congr
          intro pair _pairMember
          cases firstAt : occurrenceAtSlot pair.1 <;>
            cases secondAt : occurrenceAtSlot pair.2 <;>
              simp [List.optionalFilteredPair]
    _ = (taggedPairs.filterMap fun pair =>
          List.optionalFilteredPair
            (fun _ : (IndexedGridSegment × Cell) ×
              (IndexedGridSegment × Cell) => true)
            (occurrenceAtSlot pair.1) (occurrenceAtSlot pair.2)).flatMap
        (occurrencePairCanonicalLeftSourceKeyShiftBlockAtPeriod period) :=
          List.flatMap_toList_flatMap_eq_filterMap_flatMap
            taggedPairs
            (fun pair => List.optionalFilteredPair
              (fun _ : (IndexedGridSegment × Cell) ×
                (IndexedGridSegment × Cell) => true)
              (occurrenceAtSlot pair.1) (occurrenceAtSlot pair.2))
            (occurrencePairCanonicalLeftSourceKeyShiftBlockAtPeriod period)
    _ = ((taggedDescriptors descriptors).filterMap occurrenceAtSlot ×ˢ
          (taggedDescriptors descriptors).filterMap occurrenceAtSlot).flatMap
        (occurrencePairCanonicalLeftSourceKeyShiftBlockAtPeriod period) := by
          unfold taggedPairs
          rw [List.optionalFilteredProduct
            (fun _ : (IndexedGridSegment × Cell) ×
              (IndexedGridSegment × Cell) => true)
            (taggedDescriptors descriptors) (taggedDescriptors descriptors)
            occurrenceAtSlot occurrenceAtSlot]
          simp only [List.filter_true]
    _ = _ := by
      rw [filterMap_taggedDescriptors_occurrenceAtSlot descriptors selfIndexed]
      unfold occurrencePairCanonicalLeftSourceKeyShiftScanAtPeriod
        occurrencePairCanonicalCrossingRecordShiftScanAtPeriod
        occurrencePairCanonicalLeftSourceKeyShiftBlockAtPeriod
      rw [List.map_flatMap]

end CanonicalCrossingShiftLeftSourceKeyStream
end LeanTrominoes.PeriodicOrthocrossing
