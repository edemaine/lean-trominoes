/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorLocalSegments

/-! # Self-indexed route-descriptor occurrence blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- A descriptor stream whose stored edge indices equal its presentation
indices decomposes into blocks indexed by those stored edge indices.  The
raw hypothesis keeps this elementary factorization independent of the later
crossing-count layer. -/
theorem routeDescriptorNeighborOccurrences_eq_selfIndexedFlatMap
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2) :
    routeDescriptorNeighborOccurrences descriptors =
      descriptors.flatMap fun descriptor =>
        descriptor.neighborOccurrences descriptor.edgeIndex := by
  rw [routeDescriptorNeighborOccurrences_eq_localBlocks]
  calc
    descriptors.zipIdx.flatMap (fun tagged =>
        tagged.1.neighborOccurrences tagged.2) =
      descriptors.zipIdx.flatMap (fun tagged =>
        tagged.1.neighborOccurrences tagged.1.edgeIndex) := by
      apply List.flatMap_congr
      intro tagged taggedMember
      rw [selfIndexed tagged taggedMember]
    _ = (descriptors.zipIdx.map Prod.fst).flatMap
        (fun descriptor =>
          descriptor.neighborOccurrences descriptor.edgeIndex) := by
      rw [List.flatMap_map]
    _ = descriptors.flatMap (fun descriptor =>
        descriptor.neighborOccurrences descriptor.edgeIndex) := by
      rw [List.zipIdx_map_fst]

end LeanTrominoes.PeriodicOrthocrossing
