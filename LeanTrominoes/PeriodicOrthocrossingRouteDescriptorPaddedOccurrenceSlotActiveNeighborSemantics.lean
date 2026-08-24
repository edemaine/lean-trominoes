/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlotActiveStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlots

/-! # Active indexed slots as neighboring occurrences -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotBinaryWords

/-- Removing inactive indexed slots gives the exact neighboring-occurrence
stream for a self-indexed descriptor list. -/
theorem filterMap_taggedDescriptors_occurrenceAtSlot
    (descriptors : List RouteDescriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors) :
    (taggedDescriptors descriptors).filterMap occurrenceAtSlot =
      routeDescriptorNeighborOccurrences descriptors := by
  rw [filterMap_taggedDescriptors_occurrenceAtSlot_eq_padded]
  exact filterMap_routeDescriptorPaddedOccurrenceSlots
    descriptors selfIndexed

end RouteDescriptorOccurrenceSlotBinaryWords
end LeanTrominoes.PeriodicOrthocrossing
