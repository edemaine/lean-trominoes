/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFinRangeGetElemPad
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlotIndexData

/-! # Enumeration of fixed descriptor occurrence slots -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Increasing fixed indices enumerate exactly the padded occurrence block. -/
theorem RouteDescriptor.map_paddedNeighborOccurrenceAtSlot
    (descriptor : RouteDescriptor) :
    (List.finRange 81).map
        descriptor.paddedNeighborOccurrenceAtSlot =
      descriptor.paddedNeighborOccurrenceSlots := by
  unfold RouteDescriptor.paddedNeighborOccurrenceAtSlot
    RouteDescriptor.paddedNeighborOccurrenceSlots
  exact List.map_finRange_getElem?_eq_pad
    descriptor.selfIndexedNeighborOccurrences 81
    (descriptor.neighborOccurrences_length_le_eightyOne
      descriptor.edgeIndex)

end LeanTrominoes.PeriodicOrthocrossing
