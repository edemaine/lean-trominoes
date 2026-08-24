/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlotIndexData

/-! # Enumeration of fixed descriptor occurrence slots -/

namespace LeanTrominoes.PeriodicOrthocrossing

theorem map_finRange_get_cast
    (values : List α) (count : Nat)
    (lengthEq : values.length = count) :
    (List.finRange count).map (fun index =>
        values.get (Fin.cast lengthEq.symm index)) = values := by
  subst count
  simp

/-- Increasing fixed indices enumerate exactly the padded occurrence block. -/
theorem RouteDescriptor.map_paddedNeighborOccurrenceAtSlot
    (descriptor : RouteDescriptor) :
    (List.finRange 81).map
        descriptor.paddedNeighborOccurrenceAtSlot =
      descriptor.paddedNeighborOccurrenceSlots := by
  exact map_finRange_get_cast
    descriptor.paddedNeighborOccurrenceSlots 81
    descriptor.paddedNeighborOccurrenceSlots_length

end LeanTrominoes.PeriodicOrthocrossing
