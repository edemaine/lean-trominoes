/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierNodeKeyTemplateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingPredicateData

/-! # Carrier-key projection of crossing-node slot blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open RouteDescriptorPairAffine

@[simp] theorem Slot.map_carrierKey_carrierNodeTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor) (slot : Slot) :
    (slot.carrierNodeTemplateBlock pair).map
        (Template.mapValue CarrierNode.carrierKey) =
      slot.carrierKeyTemplateBlock pair := by
  unfold Slot.carrierNodeTemplateBlock Slot.carrierKeyTemplateBlock
  exact map_carrierKey_occurrencePairCrossingCarrierNodeTemplateBlock
    pair slot.occurrences

@[simp] theorem map_carrierKey_crossingCarrierNodeTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor) :
    (crossingCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue CarrierNode.carrierKey)) =
      crossingCarrierKeyTemplateBlocks pair := by
  simp [crossingCarrierNodeTemplateBlocks,
    crossingCarrierKeyTemplateBlocks]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
