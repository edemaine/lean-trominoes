/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorSelfIndexedNeighborOccurrences
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTerminalCarrierKeyTranslation

/-! # Membership in the global route-descriptor terminal-key stream -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Membership in one descriptor's occurrence block factors into segment
membership and the fixed neighboring-translation condition. -/
theorem mem_storedIndexNeighborOccurrences_iff
    (descriptor : RouteDescriptor)
    (indexed : IndexedGridSegment) (translate : Cell) :
    (indexed, translate) ∈
        descriptor.neighborOccurrences descriptor.edgeIndex ↔
      indexed ∈ descriptor.indexedSegments descriptor.edgeIndex ∧
        translate ∈ neighborTranslations := by
  unfold RouteDescriptor.neighborOccurrences
  constructor
  · intro member
    rw [List.mem_flatMap] at member
    rcases member with
      ⟨sourceIndexed, sourceIndexedMember, translatedMember⟩
    rw [List.mem_map] at translatedMember
    rcases translatedMember with
      ⟨sourceTranslate, sourceTranslateMember, occurrenceEq⟩
    cases occurrenceEq
    exact ⟨sourceIndexedMember, sourceTranslateMember⟩
  · rintro ⟨indexedMember, translateMember⟩
    rw [List.mem_flatMap]
    exact ⟨indexed, indexedMember,
      List.mem_map.mpr ⟨translate, translateMember, rfl⟩⟩

/-- Once an occurrence witnesses a segment in a presented descriptor, the
corresponding key belongs to the global terminal stream exactly at one of
the fixed neighboring translations. -/
theorem occurrenceCarrierKey_mem_routeDescriptorTerminal_iff
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (descriptor : RouteDescriptor) (descriptorMember : descriptor ∈ descriptors)
    (indexed : IndexedGridSegment) (originalTranslate translate : Cell)
    (originalMember : (indexed, originalTranslate) ∈
      descriptor.neighborOccurrences descriptor.edgeIndex) :
    occurrenceCarrierKey (indexed, translate) ∈
        occurrenceTerminalCarrierKeys
          (routeDescriptorNeighborOccurrences descriptors) ↔
      translate ∈ neighborTranslations := by
  constructor
  · exact translate_mem_neighborTranslations_of_mem_routeDescriptorTerminal
      descriptors indexed translate
  · intro translateMember
    have indexedMember :
        indexed ∈ descriptor.indexedSegments descriptor.edgeIndex :=
      (mem_storedIndexNeighborOccurrences_iff
        descriptor indexed originalTranslate).mp originalMember |>.1
    have occurrenceMember :
        (indexed, translate) ∈
          descriptor.neighborOccurrences descriptor.edgeIndex :=
      (mem_storedIndexNeighborOccurrences_iff
        descriptor indexed translate).mpr
          ⟨indexedMember, translateMember⟩
    rw [routeDescriptorNeighborOccurrences_eq_selfIndexedFlatMap
      descriptors selfIndexed]
    unfold occurrenceTerminalCarrierKeys
    rw [List.flatMap_assoc, List.mem_flatMap]
    refine ⟨descriptor, descriptorMember, ?_⟩
    rw [List.mem_flatMap]
    exact ⟨(indexed, translate), occurrenceMember, by simp⟩

end LeanTrominoes.PeriodicOrthocrossing
