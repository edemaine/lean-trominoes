/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingSemantics

/-! # Fixed neighboring-occurrence slots for route descriptors -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Pad one descriptor's at-most-eighty-one self-indexed neighboring
occurrences to exactly eighty-one fixed slots. -/
def RouteDescriptor.paddedNeighborOccurrenceSlots
    (descriptor : RouteDescriptor) :
    List (Option (IndexedGridSegment × Cell)) :=
  descriptor.selfIndexedNeighborOccurrences.map some ++
    List.replicate
      (81 - descriptor.selfIndexedNeighborOccurrences.length) none

/-- Every padded descriptor block has exactly eighty-one slots. -/
theorem RouteDescriptor.paddedNeighborOccurrenceSlots_length
    (descriptor : RouteDescriptor) :
    descriptor.paddedNeighborOccurrenceSlots.length = 81 := by
  unfold RouteDescriptor.paddedNeighborOccurrenceSlots
  rw [List.length_append, List.length_map, List.length_replicate]
  have bound := descriptor.neighborOccurrences_length_le_eightyOne
    descriptor.edgeIndex
  simp [RouteDescriptor.selfIndexedNeighborOccurrences,
    Nat.add_sub_of_le bound]

/-- Removing the inactive suffix recovers the descriptor's exact neighboring
occurrence list. -/
@[simp] theorem RouteDescriptor.filterMap_paddedNeighborOccurrenceSlots
    (descriptor : RouteDescriptor) :
    descriptor.paddedNeighborOccurrenceSlots.filterMap id =
      descriptor.selfIndexedNeighborOccurrences := by
  simp [RouteDescriptor.paddedNeighborOccurrenceSlots]

/-- Descriptor-major stream of fixed occurrence slots. -/
def routeDescriptorPaddedOccurrenceSlots
    (descriptors : List RouteDescriptor) :
    List (RouteDescriptor ×
      Option (IndexedGridSegment × Cell)) :=
  descriptors.flatMap fun descriptor =>
    descriptor.paddedNeighborOccurrenceSlots.map fun occurrence =>
      (descriptor, occurrence)

/-- Filtering the fixed slot stream always gives the descriptor-major
self-indexed occurrence blocks. -/
theorem filterMap_routeDescriptorPaddedOccurrenceSlots_eq_selfIndexedBlocks
    (descriptors : List RouteDescriptor) :
    (routeDescriptorPaddedOccurrenceSlots descriptors).filterMap Prod.snd =
      descriptors.flatMap
        RouteDescriptor.selfIndexedNeighborOccurrences := by
  unfold routeDescriptorPaddedOccurrenceSlots
  induction descriptors with
  | nil => rfl
  | cons descriptor descriptors induction =>
      simp [induction]
      exact descriptor.filterMap_paddedNeighborOccurrenceSlots

/-- On a self-indexed descriptor stream, filtering inactive fixed slots gives
the exact global neighboring-occurrence stream in its original order. -/
theorem filterMap_routeDescriptorPaddedOccurrenceSlots
    (descriptors : List RouteDescriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors) :
    (routeDescriptorPaddedOccurrenceSlots descriptors).filterMap Prod.snd =
      routeDescriptorNeighborOccurrences descriptors := by
  rw [filterMap_routeDescriptorPaddedOccurrenceSlots_eq_selfIndexedBlocks]
  exact (routeDescriptorNeighborOccurrences_eq_selfIndexedBlocks
    descriptors selfIndexed).symm

end LeanTrominoes.PeriodicOrthocrossing
