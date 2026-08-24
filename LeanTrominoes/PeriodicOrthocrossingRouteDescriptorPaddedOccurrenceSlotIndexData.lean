/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlotData

/-! # Indexed lookup in fixed descriptor occurrence slots -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Read the padded semantic occurrence occupying one fixed slot. -/
def RouteDescriptor.paddedNeighborOccurrenceAtSlot
    (descriptor : RouteDescriptor) (slot : Fin 81) :
    Option (IndexedGridSegment × Cell) :=
  descriptor.selfIndexedNeighborOccurrences[slot.val]?

end LeanTrominoes.PeriodicOrthocrossing
