/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeSelectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierNodeTemplateSemantics

/-! # Values of slot-major crossing carrier-node templates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

/-- One slot's fixed template block carries the exact retained boundary-node
expansion of its evaluated affine occurrence pair. -/
theorem Slot.carrierNodeTemplateBlock_values
    (slot : Slot) (pair : RouteDescriptor × RouteDescriptor) :
    (slot.carrierNodeTemplateBlock pair).map Template.value =
      (occurrencePairRetainedCrossingRecordBlockAtPeriod
        pair.1.gridSize
        (slot.occurrences.1.evalPair .first pair,
          slot.occurrences.2.evalPair .second pair)).flatMap
            crossingRecordCarrierBoundaryNodes := by
  exact occurrencePairCrossingCarrierNodeTemplateBlock_values
    pair slot.occurrences

/-- The active slot-major node list expands every accepted affine occurrence
template to its retained crossing-boundary nodes, in fixed slot order. -/
theorem crossingCarrierNodeActiveValues_eq_occurrenceScan
    (pair : TaggedDescriptor × TaggedDescriptor) :
    activeValues
        (crossingActivations (descriptorSlotPairTokens pair))
        (crossingCarrierNodeTemplateBlocks (pair.1.1, pair.2.1)) =
      (crossingSlots.filter fun slot =>
        slot.evalTokens (descriptorSlotPairTokens pair)).flatMap fun slot =>
          (occurrencePairRetainedCrossingRecordBlockAtPeriod
            pair.1.1.gridSize
            (slot.occurrences.1.evalPair .first
                (pair.1.1, pair.2.1),
              slot.occurrences.2.evalPair .second
                (pair.1.1, pair.2.1))).flatMap
                  crossingRecordCarrierBoundaryNodes := by
  rw [crossingCarrierNodeActiveValues_eq_filter_flatMap]
  apply List.flatMap_congr
  intro slot _slotMember
  exact slot.carrierNodeTemplateBlock_values
    (pair.1.1, pair.2.1)

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
