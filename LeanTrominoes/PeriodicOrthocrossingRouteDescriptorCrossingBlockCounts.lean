/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFilteredProductCount
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorLocalSegments

/-! # Descriptor-block decomposition of canonical crossing counts -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- For one fixed first occurrence, scan every descriptor's neighboring
occurrence block for accepted second occurrences. -/
def routeDescriptorCrossingRowCountAtPeriod
    (period : Nat) (first : IndexedGridSegment × Cell)
    (descriptors : List RouteDescriptor) : Nat :=
  (descriptors.zipIdx.map fun tagged =>
    List.filteredRowCount (canonicalOrientedOccurrencePairAtPeriod period)
      first (tagged.1.neighborOccurrences tagged.2)).sum

/-- Crossing count contributed by one first descriptor, retaining the exact
first-occurrence-major scan order. -/
def routeDescriptorCrossingBlockCountAtPeriod
    (period : Nat) (tagged : RouteDescriptor × Nat)
    (descriptors : List RouteDescriptor) : Nat :=
  ((tagged.1.neighborOccurrences tagged.2).map fun first =>
    routeDescriptorCrossingRowCountAtPeriod
      period first descriptors).sum

/-- One crossing-count block per first route descriptor. -/
def routeDescriptorCrossingBlockCountsAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) : List Nat :=
  descriptors.zipIdx.map fun tagged =>
    routeDescriptorCrossingBlockCountAtPeriod
      period tagged descriptors

/-- The complete descriptor crossing count is exactly the sum of the nested
descriptor/occurrence/descriptor/occurrence scan blocks. -/
theorem routeDescriptorOrientedCrossingCountAtPeriod_eq_blockCounts
    (period : Nat) (descriptors : List RouteDescriptor) :
    routeDescriptorOrientedCrossingCountAtPeriod period descriptors =
      (routeDescriptorCrossingBlockCountsAtPeriod
        period descriptors).sum := by
  unfold routeDescriptorOrientedCrossingCountAtPeriod
    routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
    routeDescriptorCrossingBlockCountsAtPeriod
    routeDescriptorCrossingBlockCountAtPeriod
    routeDescriptorCrossingRowCountAtPeriod
  change List.filteredProductCount
      (canonicalOrientedOccurrencePairAtPeriod period)
      (routeDescriptorNeighborOccurrences descriptors)
      (routeDescriptorNeighborOccurrences descriptors) = _
  rw [routeDescriptorNeighborOccurrences_eq_localBlocks]
  rw [List.filteredProductCount_flatMap_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro tagged taggedMember
  rw [List.filteredProductCount_eq_sum_rows]
  apply congrArg List.sum
  apply List.map_congr_left
  intro first firstMember
  exact List.filteredRowCount_flatMap _ _ _ _

end PeriodicOrthocrossing
end LeanTrominoes
