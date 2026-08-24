/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipePairOccurrenceMatchSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeData

/-! # Alignment of one crossing slot's source-key recipe pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairAffine
open RouteDescriptorPairSourceKeyRecipePairs
open RouteDescriptorPairFieldTags

theorem Slot.sourceKeyRecipePairBlock_matchesNode
    (slot : Slot) (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂ (MatchesNode (descriptorPairTokens pair))
      slot.sourceKeyRecipePairBlock
      (slot.carrierNodeTemplateBlock pair) := by
  unfold Slot.sourceKeyRecipePairBlock Slot.carrierNodeTemplateBlock
  exact occurrencePairCrossingSourceKeyRecipePairBlock_matchesNode
    pair slot.occurrences

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
