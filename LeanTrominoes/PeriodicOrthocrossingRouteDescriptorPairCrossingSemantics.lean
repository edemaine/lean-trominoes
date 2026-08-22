/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFilteredProductBlockCount
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCrossingMarkerBlocks
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingData

/-! # Exact factorization of crossing counts by descriptor pairs -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- For a self-indexed descriptor stream, each local occurrence block can use
the edge index stored in its descriptor instead of the external list index. -/
theorem routeDescriptorNeighborOccurrences_eq_selfIndexedBlocks
    (descriptors : List RouteDescriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors) :
    routeDescriptorNeighborOccurrences descriptors =
      descriptors.flatMap
        RouteDescriptor.selfIndexedNeighborOccurrences := by
  rw [routeDescriptorNeighborOccurrences_eq_localBlocks]
  calc
    descriptors.zipIdx.flatMap (fun tagged =>
        tagged.1.neighborOccurrences tagged.2) =
      descriptors.zipIdx.flatMap (fun tagged =>
        tagged.1.selfIndexedNeighborOccurrences) := by
      apply List.flatMap_congr
      intro tagged taggedMember
      unfold RouteDescriptor.selfIndexedNeighborOccurrences
      rw [selfIndexed tagged taggedMember]
    _ = (descriptors.zipIdx.map Prod.fst).flatMap
        RouteDescriptor.selfIndexedNeighborOccurrences := by
      rw [List.flatMap_map]
    _ = descriptors.flatMap
        RouteDescriptor.selfIndexedNeighborOccurrences := by
      rw [List.zipIdx_map_fst]

/-- The global canonical crossing count is the sum of the local counts for
the row-major ordered square of a self-indexed descriptor stream. -/
theorem routeDescriptorOrientedCrossingCountAtPeriod_eq_pairCounts
    (period : Nat) (descriptors : List RouteDescriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors) :
    routeDescriptorOrientedCrossingCountAtPeriod period descriptors =
      (routeDescriptorPairCrossingCountsAtPeriod
        period descriptors).sum := by
  unfold routeDescriptorOrientedCrossingCountAtPeriod
    routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
    routeDescriptorPairCrossingCountsAtPeriod
    routeDescriptorPairCrossingCountAtPeriod
  change List.filteredProductCount
      (canonicalOrientedOccurrencePairAtPeriod period)
      (routeDescriptorNeighborOccurrences descriptors)
      (routeDescriptorNeighborOccurrences descriptors) = _
  rw [routeDescriptorNeighborOccurrences_eq_selfIndexedBlocks
      descriptors selfIndexed]
  exact List.filteredProductCount_flatMap_blocks _ _ _ _ _

/-- Flattening the pair-major blocks emits exactly thirteen markers for each
global canonical crossing. -/
theorem routeDescriptorPairCrossingMarkerBlocksAtPeriod_flatten
    (marker : α) (period : Nat) (descriptors : List RouteDescriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors) :
    (routeDescriptorPairCrossingMarkerBlocksAtPeriod
      marker period descriptors).flatten =
      List.replicate
        (13 * routeDescriptorOrientedCrossingCountAtPeriod
          period descriptors) marker := by
  unfold routeDescriptorPairCrossingMarkerBlocksAtPeriod
    routeDescriptorPairCrossingMarkersAtPeriod
  have mapEq :
      ((descriptors ×ˢ descriptors).map fun pair =>
          List.replicate
            (13 * routeDescriptorPairCrossingCountAtPeriod period pair)
            marker) =
        (routeDescriptorPairCrossingCountsAtPeriod
          period descriptors).map fun count =>
            List.replicate (13 * count) marker := by
    unfold routeDescriptorPairCrossingCountsAtPeriod
    rw [List.map_map]
    rfl
  rw [mapEq]
  rw [flatten_map_replicate_thirteen]
  rw [routeDescriptorOrientedCrossingCountAtPeriod_eq_pairCounts
    period descriptors selfIndexed]

end PeriodicOrthocrossing
end LeanTrominoes
