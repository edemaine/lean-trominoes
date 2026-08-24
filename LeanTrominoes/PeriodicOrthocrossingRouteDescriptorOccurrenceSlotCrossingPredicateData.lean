/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingSlotData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeyTemplateData

/-! # Slot-guarded affine crossing predicates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairAffine
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- Candidate carrier-key templates for a slot and a runtime descriptor
pair. -/
def Slot.carrierKeyTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor) (slot : Slot) :=
  occurrencePairCrossingCarrierKeyTemplateBlock pair slot.occurrences

/-- Candidate carrier-key blocks aligned with `crossingSlots`. -/
def crossingCarrierKeyTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor) :=
  crossingSlots.map fun slot => slot.carrierKeyTemplateBlock pair

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
