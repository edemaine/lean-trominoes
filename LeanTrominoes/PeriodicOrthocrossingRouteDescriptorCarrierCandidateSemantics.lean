/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierCandidateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingSemantics

/-! # Occurrence semantics of route-descriptor carrier candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- For a self-indexed descriptor stream, the segment/translation candidate
scan is exactly the axis projection of the neighboring occurrence stream. -/
theorem routeDescriptorCarrierSegmentBitCandidates_eq_neighborOccurrences
    (descriptors : List RouteDescriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors) :
    routeDescriptorCarrierSegmentBitCandidates descriptors =
      (routeDescriptorNeighborOccurrences descriptors).map
        carrierOccurrenceAxisBit := by
  rw [routeDescriptorNeighborOccurrences_eq_selfIndexedBlocks
    descriptors selfIndexed]
  unfold routeDescriptorCarrierSegmentBitCandidates
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro descriptor _descriptorMember
  unfold RouteDescriptor.carrierSegmentBitCandidates
    RouteDescriptor.selfIndexedNeighborOccurrences
    RouteDescriptor.neighborOccurrences
    RouteDescriptor.indexedSegments
  rw [List.map_flatMap, List.flatMap_map]
  simp only [List.map_map]
  change
    (gridPolylineSegments descriptor.route).flatMap
        (fun segment => neighborTranslations.map fun _ =>
          (decide segment.IsHorizontal, false)) =
      (gridPolylineSegments descriptor.route).zipIdx.flatMap
        (fun taggedSegment => neighborTranslations.map fun _ =>
          (decide taggedSegment.1.IsHorizontal, false))
  conv_lhs =>
    rw [← List.zipIdx_map_fst
      (l := gridPolylineSegments descriptor.route) (i := 0)]
  rw [List.flatMap_map]

end LeanTrominoes.PeriodicOrthocrossing
