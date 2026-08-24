/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlotActiveSemantics

/-! # Active indexed descriptor occurrence-slot streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotBinaryWords

/-- Filtering all tagged descriptor blocks agrees with filtering the complete
padded semantic slot stream. -/
theorem filterMap_taggedDescriptors_occurrenceAtSlot_eq_padded
    (descriptors : List RouteDescriptor) :
    (taggedDescriptors descriptors).filterMap occurrenceAtSlot =
      (routeDescriptorPaddedOccurrenceSlots descriptors).filterMap
        Prod.snd := by
  unfold taggedDescriptors routeDescriptorPaddedOccurrenceSlots
  induction descriptors with
  | nil => rfl
  | cons descriptor descriptors induction =>
      simp only [List.flatMap_cons, List.filterMap_append,
        List.filterMap_map]
      simp only [Function.comp_def]
      rw [filterMap_finRange_occurrenceAtSlot, induction]
      rfl

end RouteDescriptorOccurrenceSlotBinaryWords
end LeanTrominoes.PeriodicOrthocrossing
