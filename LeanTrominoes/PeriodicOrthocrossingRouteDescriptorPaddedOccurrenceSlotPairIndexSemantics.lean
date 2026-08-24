/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlotIndexSemantics

/-! # Pair semantics of indexed descriptor occurrence slots -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotBinaryWords

/-- Replace one tagged slot index by its padded semantic occurrence value. -/
def paddedOccurrence
    (tagged : TaggedDescriptor) :
    RouteDescriptor × Option (IndexedGridSegment × Cell) :=
  (tagged.1, occurrenceAtSlot tagged)

/-- Replacing both indices in the tagged-descriptor square gives exactly the
row-major square of the padded semantic occurrence stream. -/
theorem map_taggedDescriptorPair_paddedOccurrence
    (descriptors : List RouteDescriptor) :
    (taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors).map (fun pair =>
          (paddedOccurrence pair.1, paddedOccurrence pair.2)) =
      routeDescriptorPaddedOccurrenceSlots descriptors ×ˢ
        routeDescriptorPaddedOccurrenceSlots descriptors := by
  calc
    _ = ((taggedDescriptors descriptors).map paddedOccurrence ×ˢ
          (taggedDescriptors descriptors).map paddedOccurrence) := by
      symm
      exact product_map_map
        (taggedDescriptors descriptors)
        (taggedDescriptors descriptors)
        paddedOccurrence paddedOccurrence
    _ = _ := by
      rw [show (taggedDescriptors descriptors).map paddedOccurrence =
          routeDescriptorPaddedOccurrenceSlots descriptors by
        exact map_taggedDescriptors_occurrenceAtSlot descriptors]

end RouteDescriptorOccurrenceSlotBinaryWords
end LeanTrominoes.PeriodicOrthocrossing
