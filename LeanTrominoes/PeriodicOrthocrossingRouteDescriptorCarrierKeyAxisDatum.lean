/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFields
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorLocalSegments

/-! # Carrier-key axis data recovered from route descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorCarrierKeyAxisDatum

abbrev CarrierKey := Nat × Nat × Cell

/-- The carrier key of one reconstructed neighboring occurrence. -/
def occurrenceKey (occurrence : IndexedGridSegment × Cell) : CarrierKey :=
  PeriodicGridDrawing.SegmentOccurrenceKey occurrence.1 occurrence.2

/-- Within the descriptor-reconstructed segment list, route and segment
indices uniquely determine the complete indexed segment. -/
theorem indexedSegment_eq_of_indices_eq
    (descriptors : List RouteDescriptor)
    {first second : IndexedGridSegment}
    (firstMember : first ∈ routeDescriptorIndexedSegments descriptors)
    (secondMember : second ∈ routeDescriptorIndexedSegments descriptors)
    (routeEq : first.routeIndex = second.routeIndex)
    (segmentEq : first.segmentIndex = second.segmentIndex) :
    first = second := by
  unfold routeDescriptorIndexedSegments at firstMember secondMember
  rcases List.mem_flatMap.mp firstMember with
    ⟨firstRoute, firstRouteMember, firstMember⟩
  rcases List.mem_map.mp firstMember with
    ⟨firstSegment, firstSegmentMember, firstEq⟩
  rcases List.mem_flatMap.mp secondMember with
    ⟨secondRoute, secondRouteMember, secondMember⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondSegment, secondSegmentMember, secondEq⟩
  subst first
  subst second
  have routesEq := tagged_eq_of_mem_zipIdx_of_snd_eq
    firstRouteMember secondRouteMember routeEq
  subst secondRoute
  have segmentsEq := tagged_eq_of_mem_zipIdx_of_snd_eq
    firstSegmentMember secondSegmentMember segmentEq
  subst secondSegment
  rfl

/-- A neighboring occurrence's indexed segment belongs to the reconstructed
global indexed-segment list. -/
theorem indexed_mem_of_neighbor_mem
    (descriptors : List RouteDescriptor)
    {occurrence : IndexedGridSegment × Cell}
    (member : occurrence ∈ routeDescriptorNeighborOccurrences descriptors) :
    occurrence.1 ∈ routeDescriptorIndexedSegments descriptors := by
  unfold routeDescriptorNeighborOccurrences at member
  rcases List.mem_flatMap.mp member with
    ⟨indexed, indexedMember, occurrenceMember⟩
  rcases List.mem_map.mp occurrenceMember with
    ⟨translate, _translateMember, occurrenceEq⟩
  subst occurrence
  exact indexedMember

/-- Equal carrier keys of reconstructed neighboring occurrences have the
same complete indexed segment and hence the same axis. -/
theorem indexed_eq_of_occurrenceKey_eq
    (descriptors : List RouteDescriptor)
    {first second : IndexedGridSegment × Cell}
    (firstMember : first ∈ routeDescriptorNeighborOccurrences descriptors)
    (secondMember : second ∈ routeDescriptorNeighborOccurrences descriptors)
    (keyEq : occurrenceKey first = occurrenceKey second) :
    first.1 = second.1 := by
  apply indexedSegment_eq_of_indices_eq descriptors
    (indexed_mem_of_neighbor_mem descriptors firstMember)
    (indexed_mem_of_neighbor_mem descriptors secondMember)
  · exact congrArg Prod.fst keyEq
  · exact congrArg (fun key => key.2.1) keyEq

/-- Zero for an absent candidate; otherwise the horizontal-axis bit of the
indexed segment named by the key's route and segment coordinates, with zero
as an irrelevant default for malformed keys.  Looking up the indexed segment
rather than a neighboring occurrence makes the datum independent of the
translation coordinate, including padded crossing candidates outside the
neighboring translation window. -/
noncomputable def value (descriptors : List RouteDescriptor) :
    Option CarrierKey → Nat
  | none => 0
  | some key =>
      if witness : ∃ indexed ∈ routeDescriptorIndexedSegments descriptors,
          indexed.routeIndex = key.1 ∧
            indexed.segmentIndex = key.2.1 then
        let indexed := Classical.choose witness
        FixedAxisUnaryFields.value true
          (decide indexed.segment.IsHorizontal)
      else
        0

@[simp] theorem value_none (descriptors : List RouteDescriptor) :
    value descriptors none = 0 := rfl

/-- Every reconstructed indexed segment recovers its own orientation from
the datum at any translation coordinate. -/
theorem value_some_segmentOccurrenceKey
    (descriptors : List RouteDescriptor)
    (indexed : IndexedGridSegment) (translate : Cell)
    (member : indexed ∈ routeDescriptorIndexedSegments descriptors) :
    value descriptors
        (some (PeriodicGridDrawing.SegmentOccurrenceKey indexed translate)) =
      FixedAxisUnaryFields.value true
        (decide indexed.segment.IsHorizontal) := by
  rw [value]
  split
  · rename_i witness
    let chosen := Classical.choose witness
    have chosenSpec := Classical.choose_spec witness
    have chosenSpec' :
        chosen ∈ routeDescriptorIndexedSegments descriptors ∧
          chosen.routeIndex =
            (PeriodicGridDrawing.SegmentOccurrenceKey indexed translate).1 ∧
          chosen.segmentIndex =
            (PeriodicGridDrawing.SegmentOccurrenceKey indexed translate).2.1 := by
      simpa [chosen] using chosenSpec
    have indexedEq : chosen = indexed :=
      indexedSegment_eq_of_indices_eq descriptors
        chosenSpec'.1 member
        (by simpa [
          PeriodicGridDrawing.SegmentOccurrenceKey] using chosenSpec'.2.1)
        (by simpa [
          PeriodicGridDrawing.SegmentOccurrenceKey] using chosenSpec'.2.2)
    change FixedAxisUnaryFields.value true
        (decide chosen.segment.IsHorizontal) = _
    rw [indexedEq]
  · rename_i notWitness
    exact False.elim (notWitness
      ⟨indexed, member, by
        simp [PeriodicGridDrawing.SegmentOccurrenceKey]⟩)

/-- Every listed neighboring occurrence recovers its own orientation from
the key datum. -/
theorem value_some_occurrenceKey
    (descriptors : List RouteDescriptor)
    (occurrence : IndexedGridSegment × Cell)
    (member : occurrence ∈ routeDescriptorNeighborOccurrences descriptors) :
    value descriptors (some (occurrenceKey occurrence)) =
      FixedAxisUnaryFields.value true
        (decide occurrence.1.segment.IsHorizontal) := by
  exact value_some_segmentOccurrenceKey descriptors
    occurrence.1 occurrence.2
    (indexed_mem_of_neighbor_mem descriptors member)

end RouteDescriptorCarrierKeyAxisDatum
end LeanTrominoes.PeriodicOrthocrossing

end
