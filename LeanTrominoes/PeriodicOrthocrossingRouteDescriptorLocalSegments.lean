/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCrossingPairData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorSegmentBounds

/-! # Per-descriptor segment and neighboring-occurrence blocks -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Indexed segments contributed by one descriptor at its supplied route
index. -/
def RouteDescriptor.indexedSegments
    (descriptor : RouteDescriptor) (routeIndex : Nat) :
    List IndexedGridSegment :=
  (gridPolylineSegments descriptor.route).zipIdx.map fun taggedSegment =>
    ⟨routeIndex, taggedSegment.2, taggedSegment.1⟩

/-- All nine neighboring translations of one descriptor's indexed segments. -/
def RouteDescriptor.neighborOccurrences
    (descriptor : RouteDescriptor) (routeIndex : Nat) :
    List (IndexedGridSegment × Cell) :=
  (descriptor.indexedSegments routeIndex).flatMap fun indexed =>
    neighborTranslations.map fun translate => (indexed, translate)

/-- The global reconstructed segment list is a descriptor-major flat map of
the local indexed segment blocks. -/
theorem routeDescriptorIndexedSegments_eq_localBlocks
    (descriptors : List RouteDescriptor) :
    routeDescriptorIndexedSegments descriptors =
      descriptors.zipIdx.flatMap fun tagged =>
        tagged.1.indexedSegments tagged.2 := by
  unfold routeDescriptorIndexedSegments RouteDescriptor.indexedSegments
  rw [List.zipIdx_map, List.flatMap_map]
  rfl

/-- The global neighboring occurrence stream has the same descriptor-major
block decomposition. -/
theorem routeDescriptorNeighborOccurrences_eq_localBlocks
    (descriptors : List RouteDescriptor) :
    routeDescriptorNeighborOccurrences descriptors =
      descriptors.zipIdx.flatMap fun tagged =>
        tagged.1.neighborOccurrences tagged.2 := by
  rw [show routeDescriptorNeighborOccurrences descriptors =
      (routeDescriptorIndexedSegments descriptors).flatMap fun indexed =>
        neighborTranslations.map fun translate => (indexed, translate) by
    rfl]
  rw [routeDescriptorIndexedSegments_eq_localBlocks]
  simp only [List.flatMap_assoc, RouteDescriptor.neighborOccurrences]

/-- One descriptor contributes at most nine indexed segments. -/
theorem RouteDescriptor.indexedSegments_length_le_nine
    (descriptor : RouteDescriptor) (routeIndex : Nat) :
    (descriptor.indexedSegments routeIndex).length ≤ 9 := by
  simp only [RouteDescriptor.indexedSegments, List.length_map,
    List.length_zipIdx]
  exact descriptor.route_segments_length_le_nine

/-- Including the fixed neighboring translations, one descriptor contributes
at most eighty-one segment occurrences. -/
theorem RouteDescriptor.neighborOccurrences_length_le_eightyOne
    (descriptor : RouteDescriptor) (routeIndex : Nat) :
    (descriptor.neighborOccurrences routeIndex).length ≤ 81 := by
  unfold RouteDescriptor.neighborOccurrences
  rw [List.length_flatMap]
  simp only [List.length_map]
  have segmentsLe := descriptor.indexedSegments_length_le_nine routeIndex
  simp [neighborTranslations, neighborCoordinates]
  omega

end PeriodicOrthocrossing
end LeanTrominoes
