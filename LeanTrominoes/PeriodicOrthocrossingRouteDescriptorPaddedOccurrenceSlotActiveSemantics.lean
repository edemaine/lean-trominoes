/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFilterMapMapIdentity
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlotIndexEnumeration

/-! # Active indexed descriptor occurrence slots -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotBinaryWords

/-- Removing inactive fixed indices from one descriptor block agrees exactly
with filtering its padded semantic occurrence list. -/
theorem filterMap_finRange_occurrenceAtSlot
    (descriptor : RouteDescriptor) :
    (List.finRange 81).filterMap (fun slot =>
        occurrenceAtSlot (descriptor, slot)) =
      descriptor.paddedNeighborOccurrenceSlots.filterMap id := by
  exact List.filterMap_eq_filterMap_id_of_map_eq
    (List.finRange 81) descriptor.paddedNeighborOccurrenceAtSlot
    descriptor.paddedNeighborOccurrenceSlots
    descriptor.map_paddedNeighborOccurrenceAtSlot

end RouteDescriptorOccurrenceSlotBinaryWords
end LeanTrominoes.PeriodicOrthocrossing
