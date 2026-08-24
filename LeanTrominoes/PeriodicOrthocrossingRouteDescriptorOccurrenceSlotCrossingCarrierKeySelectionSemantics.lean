/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockMappedSelection
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyData

/-! # Selection semantics of slot-major crossing carrier keys -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- Compact carrier-key selection is exactly the flat map over the accepted
fixed crossing slots. -/
theorem crossingCarrierKeyActiveValues_eq_filter_flatMap
    (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingCarrierKeyActiveValues pair =
      (crossingSlots.filter fun slot =>
        slot.evalTokens (descriptorSlotPairTokens pair)).flatMap fun slot =>
          (slot.carrierKeyTemplateBlock
            (pair.1.1, pair.2.1)).map Template.value := by
  unfold crossingCarrierKeyActiveValues crossingActivations
    crossingCarrierKeyTemplateBlocks
  exact activeValues_map_eq_filter_flatMap
    crossingSlots
    (fun slot => slot.evalTokens (descriptorSlotPairTokens pair))
    (fun slot => slot.carrierKeyTemplateBlock
      (pair.1.1, pair.2.1))

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
