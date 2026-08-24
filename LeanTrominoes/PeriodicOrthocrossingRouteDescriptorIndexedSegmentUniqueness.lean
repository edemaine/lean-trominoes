/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCrossingPairData

/-! # Indexed-segment uniqueness in route-descriptor streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorCarrierKeyAxisDatum

abbrev CarrierKey := Nat × Nat × Cell

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
same complete indexed segment. -/
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

end RouteDescriptorCarrierKeyAxisDatum
end LeanTrominoes.PeriodicOrthocrossing
