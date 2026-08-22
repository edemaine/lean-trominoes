/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFilteredProductCount
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorLocalSegments

/-! # Crossing counts local to ordered route-descriptor pairs -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Every descriptor stores its own zero-based presentation position. -/
def RouteDescriptorList.SelfIndexed
    (descriptors : List RouteDescriptor) : Prop :=
  ∀ tagged ∈ descriptors.zipIdx,
    tagged.1.edgeIndex = tagged.2

/-- Neighboring segment occurrences of a descriptor indexed by the edge index
stored in that same descriptor record. -/
def RouteDescriptor.selfIndexedNeighborOccurrences
    (descriptor : RouteDescriptor) :
    List (IndexedGridSegment × Cell) :=
  descriptor.neighborOccurrences descriptor.edgeIndex

/-- Number of canonical oriented crossings contributed by one ordered pair of
descriptor records at an explicit drawing period. -/
def routeDescriptorPairCrossingCountAtPeriod
    (period : Nat) (pair : RouteDescriptor × RouteDescriptor) : Nat :=
  List.filteredProductCount
    (canonicalOrientedOccurrencePairAtPeriod period)
    pair.1.selfIndexedNeighborOccurrences
    pair.2.selfIndexedNeighborOccurrences

/-- One local crossing count for every row-major ordered descriptor pair. -/
def routeDescriptorPairCrossingCountsAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) : List Nat :=
  (descriptors ×ˢ descriptors).map
    (routeDescriptorPairCrossingCountAtPeriod period)

/-- Thirteen identical output markers for every crossing contributed by one
ordered descriptor pair. -/
def routeDescriptorPairCrossingMarkersAtPeriod
    (marker : α) (period : Nat)
    (pair : RouteDescriptor × RouteDescriptor) : List α :=
  List.replicate
    (13 * routeDescriptorPairCrossingCountAtPeriod period pair) marker

/-- One crossing-marker block for every row-major descriptor pair. -/
def routeDescriptorPairCrossingMarkerBlocksAtPeriod
    (marker : α) (period : Nat)
    (descriptors : List RouteDescriptor) : List (List α) :=
  (descriptors ×ˢ descriptors).map
    (routeDescriptorPairCrossingMarkersAtPeriod marker period)

end PeriodicOrthocrossing
end LeanTrominoes
