/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlotIndexEnumeration

/-! # Index semantics of fixed descriptor occurrence slots -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotBinaryWords

/-- Replacing every tagged slot index by its padded semantic value recovers
the exact descriptor-major padded occurrence stream. -/
theorem map_taggedDescriptors_occurrenceAtSlot
    (descriptors : List RouteDescriptor) :
    (taggedDescriptors descriptors).map (fun tagged =>
        (tagged.1, occurrenceAtSlot tagged)) =
      routeDescriptorPaddedOccurrenceSlots descriptors := by
  unfold taggedDescriptors routeDescriptorPaddedOccurrenceSlots
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro descriptor _
  rw [List.map_map]
  change (List.finRange 81).map (fun slot =>
      (descriptor,
        descriptor.paddedNeighborOccurrenceAtSlot slot)) = _
  calc
    _ = ((List.finRange 81).map
          descriptor.paddedNeighborOccurrenceAtSlot).map
        (fun occurrence => (descriptor, occurrence)) := by
      simp only [List.map_map, Function.comp_def]
    _ = _ := congrArg
      (List.map fun occurrence => (descriptor, occurrence))
      descriptor.map_paddedNeighborOccurrenceAtSlot

end RouteDescriptorOccurrenceSlotBinaryWords
end LeanTrominoes.PeriodicOrthocrossing
