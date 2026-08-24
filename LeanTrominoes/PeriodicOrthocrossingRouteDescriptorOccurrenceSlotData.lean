/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotBinaryWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlotIndexData

/-! # Semantic values of indexed descriptor occurrence slots -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotBinaryWords

/-- Read the padded semantic occurrence occupying one tagged descriptor
slot. -/
def occurrenceAtSlot (tagged : TaggedDescriptor) :
    Option (IndexedGridSegment × Cell) :=
  tagged.1.paddedNeighborOccurrenceAtSlot tagged.2

end RouteDescriptorOccurrenceSlotBinaryWords
end LeanTrominoes.PeriodicOrthocrossing
