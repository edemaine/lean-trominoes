/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeySelectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeySlotValueSemantics

/-! # Values of slot-major crossing carrier-key templates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

/-- One slot's fixed template block carries its exact graph-free retained
carrier-key values. -/
theorem Slot.carrierKeyTemplateBlock_values
    (slot : Slot) (pair : RouteDescriptor × RouteDescriptor) :
    (slot.carrierKeyTemplateBlock pair).map Template.value =
      occurrencePairCarrierKeyBlock
        (slot.occurrences.1.evalPair .first pair,
          slot.occurrences.2.evalPair .second pair) := by
  exact occurrencePairCrossingCarrierKeyTemplateBlock_values
    pair slot.occurrences

/-- The active slot-major carrier list is the retained carrier-key expansion
of each accepted affine occurrence template, in fixed slot order. -/
theorem crossingCarrierKeyActiveValues_eq_occurrenceScan
    (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingCarrierKeyActiveValues pair =
      (crossingSlots.filter fun slot =>
        slot.evalTokens (descriptorSlotPairTokens pair)).flatMap fun slot =>
          occurrencePairCarrierKeyBlock
            (slot.occurrences.1.evalPair .first (pair.1.1, pair.2.1),
              slot.occurrences.2.evalPair .second
                (pair.1.1, pair.2.1)) := by
  rw [crossingCarrierKeyActiveValues_eq_filter_flatMap]
  apply List.flatMap_congr
  intro slot _slotMember
  exact slot.carrierKeyTemplateBlock_values (pair.1.1, pair.2.1)

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
