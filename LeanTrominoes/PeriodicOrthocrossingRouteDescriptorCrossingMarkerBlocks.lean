/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCrossingBlockCounts

/-! # Per-descriptor marker blocks for canonical crossings -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Emit thirteen identical markers per accepted crossing in each first-route
block. -/
def routeDescriptorCrossingMarkerBlocks
    (marker : α) (descriptors : List RouteDescriptor) : List (List α) :=
  (routeDescriptorCrossingBlockCountsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).map
    fun count => List.replicate (13 * count) marker

theorem flatten_map_replicate_thirteen
    (marker : α) (counts : List Nat) :
    (counts.map fun count =>
      List.replicate (13 * count) marker).flatten =
        List.replicate (13 * counts.sum) marker := by
  induction counts with
  | nil => rfl
  | cons count counts induction =>
      simp only [List.map_cons, List.flatten_cons, List.sum_cons, induction]
      rw [← List.replicate_add]
      congr 2
      omega

/-- Flattening the nested scan blocks yields exactly thirteen markers per
canonical descriptor crossing. -/
theorem routeDescriptorCrossingMarkerBlocks_flatten
    (marker : α) (descriptors : List RouteDescriptor) :
    (routeDescriptorCrossingMarkerBlocks marker descriptors).flatten =
      List.replicate
        (13 * routeDescriptorOrientedCrossingCount descriptors) marker := by
  unfold routeDescriptorCrossingMarkerBlocks
  rw [flatten_map_replicate_thirteen]
  unfold routeDescriptorOrientedCrossingCount
    routeDescriptorOrientedCrossingOccurrencePairs
  have countEq :=
    routeDescriptorOrientedCrossingCountAtPeriod_eq_blockCounts
      (routeDescriptorStreamGridSize descriptors) descriptors
  unfold routeDescriptorOrientedCrossingCountAtPeriod at countEq
  rw [← countEq]

end PeriodicOrthocrossing
end LeanTrominoes
