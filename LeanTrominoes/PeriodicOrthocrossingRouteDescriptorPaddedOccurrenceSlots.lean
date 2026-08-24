/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlotData

/-! # Fixed neighboring-occurrence slots for route descriptors -/

namespace LeanTrominoes.PeriodicOrthocrossing

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
