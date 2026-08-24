/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipePairSlotMatchSemantics

/-! # Complete crossing source-key recipe-pair alignment -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairSourceKeyRecipePairs
open RouteDescriptorPairFieldTags

theorem crossingSourceKeyRecipePairBlocks_matchNode
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (List.Forall₂ (MatchesNode (descriptorPairTokens pair)))
      crossingSourceKeyRecipePairBlocks
      (crossingCarrierNodeTemplateBlocks pair) := by
  unfold crossingSourceKeyRecipePairBlocks
    crossingCarrierNodeTemplateBlocks
  induction crossingSlots with
  | nil => exact List.Forall₂.nil
  | cons slot slots induction =>
      exact List.Forall₂.cons
        (slot.sourceKeyRecipePairBlock_matchesNode pair) induction

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
