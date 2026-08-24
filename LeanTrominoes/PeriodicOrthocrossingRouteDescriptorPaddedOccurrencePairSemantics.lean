/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListOptionalFilteredProduct
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlots

/-! # Exact crossing order from fixed neighboring-occurrence slots -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Form the row-major square of all fixed descriptor occurrence slots and
retain precisely the active canonical crossing pairs. -/
def paddedRouteDescriptorOrientedCrossingOccurrencePairsAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    List ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :=
  (routeDescriptorPaddedOccurrenceSlots descriptors ×ˢ
      routeDescriptorPaddedOccurrenceSlots descriptors).filterMap fun pair =>
    List.optionalFilteredPair
      (canonicalOrientedOccurrencePairAtPeriod period)
      pair.1.2 pair.2.2

/-- For self-indexed descriptors, filtering the fixed-slot square preserves
the exact global occurrence-major order of canonical crossing pairs. -/
theorem paddedRouteDescriptorOrientedCrossingOccurrencePairsAtPeriod_eq
    (period : Nat) (descriptors : List RouteDescriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors) :
    paddedRouteDescriptorOrientedCrossingOccurrencePairsAtPeriod
        period descriptors =
      routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
        period descriptors := by
  unfold paddedRouteDescriptorOrientedCrossingOccurrencePairsAtPeriod
    routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
  rw [List.optionalFilteredProduct]
  rw [filterMap_routeDescriptorPaddedOccurrenceSlots descriptors selfIndexed]

end LeanTrominoes.PeriodicOrthocrossing
