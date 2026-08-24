/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyOrderData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingData

/-! # Membership in one descriptor's terminal carrier keys -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- A self-indexed neighboring occurrence consists exactly of one indexed
segment from the descriptor and one of the nine neighboring translations. -/
theorem mem_selfIndexedNeighborOccurrences_iff
    (descriptor : RouteDescriptor)
    (indexed : IndexedGridSegment) (translate : Cell) :
    (indexed, translate) ∈ descriptor.selfIndexedNeighborOccurrences ↔
      indexed ∈ descriptor.indexedSegments descriptor.edgeIndex ∧
        translate ∈ neighborTranslations := by
  unfold RouteDescriptor.selfIndexedNeighborOccurrences
    RouteDescriptor.neighborOccurrences
  constructor
  · intro member
    rw [List.mem_flatMap] at member
    rcases member with
      ⟨otherIndexed, indexedMember, translateMember⟩
    rw [List.mem_map] at translateMember
    rcases translateMember with
      ⟨otherTranslate, otherTranslateMember, occurrenceEq⟩
    cases occurrenceEq
    exact ⟨indexedMember, otherTranslateMember⟩
  · rintro ⟨indexedMember, translateMember⟩
    rw [List.mem_flatMap]
    exact ⟨indexed, indexedMember,
      List.mem_map.mpr ⟨translate, translateMember, rfl⟩⟩

/-- Once one occurrence witnesses that an indexed segment belongs to the
descriptor, its carrier key is terminal-supported exactly at neighboring
translations. -/
theorem occurrenceCarrierKey_mem_selfIndexedTerminal_iff
    (descriptor : RouteDescriptor)
    (indexed : IndexedGridSegment) (originalTranslate translate : Cell)
    (originalMember :
      (indexed, originalTranslate) ∈
        descriptor.selfIndexedNeighborOccurrences) :
    occurrenceCarrierKey (indexed, translate) ∈
        occurrenceTerminalCarrierKeys
          descriptor.selfIndexedNeighborOccurrences ↔
      translate ∈ neighborTranslations := by
  constructor
  · intro keyMember
    unfold occurrenceTerminalCarrierKeys at keyMember
    rw [List.mem_flatMap] at keyMember
    rcases keyMember with ⟨occurrence, occurrenceMember, keyMember⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self]
      at keyMember
    rcases occurrence with ⟨otherIndexed, otherTranslate⟩
    have otherTranslateMember : otherTranslate ∈ neighborTranslations :=
      (mem_selfIndexedNeighborOccurrences_iff
        descriptor otherIndexed otherTranslate).mp occurrenceMember |>.2
    have translateEq : translate = otherTranslate := by
      have coordinateEq := congrArg
        (fun key : Nat × Nat × Cell => key.2.2) keyMember
      simpa [occurrenceCarrierKey,
        PeriodicGridDrawing.SegmentOccurrenceKey] using coordinateEq
    simpa [translateEq] using otherTranslateMember
  · intro translateMember
    have indexedMember :
        indexed ∈ descriptor.indexedSegments descriptor.edgeIndex :=
      (mem_selfIndexedNeighborOccurrences_iff
        descriptor indexed originalTranslate).mp originalMember |>.1
    have occurrenceMember :
        (indexed, translate) ∈
          descriptor.selfIndexedNeighborOccurrences :=
      (mem_selfIndexedNeighborOccurrences_iff
        descriptor indexed translate).mpr
          ⟨indexedMember, translateMember⟩
    unfold occurrenceTerminalCarrierKeys
    rw [List.mem_flatMap]
    exact ⟨(indexed, translate), occurrenceMember, by simp⟩

end LeanTrominoes.PeriodicOrthocrossing
