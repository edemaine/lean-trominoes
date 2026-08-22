/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingData

/-! # Constant bounds for descriptor-pair crossing outputs -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Each descriptor pair has at most `81 * 81` neighboring segment-occurrence
pairs to test. -/
theorem routeDescriptorPairCrossingCountAtPeriod_le
    (period : Nat) (pair : RouteDescriptor × RouteDescriptor) :
    routeDescriptorPairCrossingCountAtPeriod period pair ≤ 81 * 81 := by
  unfold routeDescriptorPairCrossingCountAtPeriod List.filteredProductCount
  calc
    ((pair.1.selfIndexedNeighborOccurrences ×ˢ
        pair.2.selfIndexedNeighborOccurrences).filter
          (canonicalOrientedOccurrencePairAtPeriod period)).length ≤
        (pair.1.selfIndexedNeighborOccurrences ×ˢ
          pair.2.selfIndexedNeighborOccurrences).length :=
      List.length_filter_le _ _
    _ = pair.1.selfIndexedNeighborOccurrences.length *
          pair.2.selfIndexedNeighborOccurrences.length := by
      simp only [List.length_product]
    _ ≤ 81 * 81 := Nat.mul_le_mul
      (pair.1.neighborOccurrences_length_le_eightyOne pair.1.edgeIndex)
      (pair.2.neighborOccurrences_length_le_eightyOne pair.2.edgeIndex)

/-- Consequently, a descriptor pair emits at most `13 * 6561` identical
crossing markers. -/
theorem routeDescriptorPairCrossingMarkersAtPeriod_length_le
    (marker : α) (period : Nat)
    (pair : RouteDescriptor × RouteDescriptor) :
    (routeDescriptorPairCrossingMarkersAtPeriod marker period pair).length ≤
      13 * (81 * 81) := by
  simp only [routeDescriptorPairCrossingMarkersAtPeriod,
    List.length_replicate]
  exact Nat.mul_le_mul_left 13
    (routeDescriptorPairCrossingCountAtPeriod_le period pair)

end PeriodicOrthocrossing
end LeanTrominoes
