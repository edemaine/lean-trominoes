/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyOrderData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCrossingPairData

/-! # Translation support of route-descriptor terminal carrier keys -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Every key in the reconstructed terminal stream has one of the fixed
neighboring translations. -/
theorem translate_mem_neighborTranslations_of_mem_routeDescriptorTerminal
    (descriptors : List RouteDescriptor)
    (indexed : IndexedGridSegment) (translate : Cell)
    (member : occurrenceCarrierKey (indexed, translate) ∈
      occurrenceTerminalCarrierKeys
        (routeDescriptorNeighborOccurrences descriptors)) :
    translate ∈ neighborTranslations := by
  unfold occurrenceTerminalCarrierKeys at member
  rw [List.mem_flatMap] at member
  rcases member with ⟨occurrence, occurrenceMember, keyMember⟩
  rcases occurrence with ⟨otherIndexed, otherTranslate⟩
  have otherTranslateMember : otherTranslate ∈ neighborTranslations := by
    unfold routeDescriptorNeighborOccurrences at occurrenceMember
    rw [List.mem_flatMap] at occurrenceMember
    rcases occurrenceMember with
      ⟨sourceIndexed, _sourceIndexedMember, translatedMember⟩
    rw [List.mem_map] at translatedMember
    rcases translatedMember with
      ⟨sourceTranslate, sourceTranslateMember, occurrenceEq⟩
    cases occurrenceEq
    exact sourceTranslateMember
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self]
    at keyMember
  have translateEq : translate = otherTranslate := by
    have coordinateEq := congrArg
      (fun key : Nat × Nat × Cell => key.2.2) keyMember
    simpa [occurrenceCarrierKey,
      PeriodicGridDrawing.SegmentOccurrenceKey] using coordinateEq
  simpa [translateEq] using otherTranslateMember

end LeanTrominoes.PeriodicOrthocrossing
