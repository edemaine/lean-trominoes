/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeSemantics

/-! # Alignment of crossing carrier-key recipes and templates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairCarrierKeyWordRecipes

/-- Every crossing recipe is aligned with the semantic template obtained
from the descriptors underlying the same canonical slot-pair block. -/
theorem crossingCarrierKeyRecipeBlocks_match
    (pair : TaggedDescriptor × TaggedDescriptor) :
    List.Forall₂
      (List.Forall₂ (Recipe.Matches
        (descriptorTokens (descriptorSlotPairTokens pair))))
      crossingCarrierKeyRecipeBlocks
      (crossingCarrierKeyTemplateBlocks (pair.1.1, pair.2.1)) := by
  rw [descriptorTokens_descriptorSlotPairTokens]
  rw [← map_map_template_crossingCarrierKeyRecipeBlocks
    (pair.1.1, pair.2.1)]
  induction crossingCarrierKeyRecipeBlocks with
  | nil => exact List.Forall₂.nil
  | cons block blocks induction =>
      apply List.Forall₂.cons
      · induction block with
        | nil => exact List.Forall₂.nil
        | cons recipe recipes induction =>
            exact List.Forall₂.cons
              (recipe.matches_template_descriptorPairTokens
                (pair.1.1, pair.2.1))
              induction
      · exact induction

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
