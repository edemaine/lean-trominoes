/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListOptionalFilteredProduct
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlotActiveNeighborSemantics

/-! # Crossing filter semantics of indexed descriptor occurrence slots -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotBinaryWords

/-- Canonically filtering the indexed slot square gives the exact global
crossing-pair stream in occurrence-major order. -/
theorem filterMap_taggedDescriptorPairs_eq_crossings
    (period : Nat) (descriptors : List RouteDescriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors) :
    (taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors).filterMap (fun pair =>
          List.optionalFilteredPair
            (canonicalOrientedOccurrencePairAtPeriod period)
            (occurrenceAtSlot pair.1) (occurrenceAtSlot pair.2)) =
      routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
        period descriptors := by
  unfold routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
  rw [List.optionalFilteredProduct]
  rw [filterMap_taggedDescriptors_occurrenceAtSlot
    descriptors selfIndexed]

end RouteDescriptorOccurrenceSlotBinaryWords
end LeanTrominoes.PeriodicOrthocrossing
