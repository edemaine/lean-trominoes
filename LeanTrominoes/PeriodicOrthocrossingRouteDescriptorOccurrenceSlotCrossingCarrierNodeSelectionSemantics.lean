/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockMappedSelection
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeData

/-! # Selection semantics of slot-major crossing carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- Compact carrier-node selection is exactly the flat map over the accepted
fixed crossing slots. -/
theorem crossingCarrierNodeActiveValues_eq_filter_flatMap
    (pair : TaggedDescriptor × TaggedDescriptor) :
    activeValues
        (crossingActivations (descriptorSlotPairTokens pair))
        (crossingCarrierNodeTemplateBlocks (pair.1.1, pair.2.1)) =
      (crossingSlots.filter fun slot =>
        slot.evalTokens (descriptorSlotPairTokens pair)).flatMap fun slot =>
          (slot.carrierNodeTemplateBlock
            (pair.1.1, pair.2.1)).map Template.value := by
  unfold crossingActivations crossingCarrierNodeTemplateBlocks
  exact activeValues_map_eq_filter_flatMap
    crossingSlots
    (fun slot => slot.evalTokens (descriptorSlotPairTokens pair))
    (fun slot => slot.carrierNodeTemplateBlock
      (pair.1.1, pair.2.1))

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
