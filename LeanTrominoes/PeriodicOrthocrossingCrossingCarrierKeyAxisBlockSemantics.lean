/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisBlockActivesSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisValueData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeActivationSemantics

/-! # Structural semantics of crossing carrier-key axis blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorOccurrenceSlotBinaryWords

/-- Every crossing recipe block has the same length as its explicit axis
block. -/
theorem crossingCarrierKeyRecipeBlocks_forall₂_axisBlocks_length :
    List.Forall₂ (fun block axes => block.length = axes.length)
      crossingCarrierKeyRecipeBlocks
      crossingCarrierKeyRecipeAxisBlocks := by
  unfold crossingCarrierKeyRecipeAxisBlocks
  induction crossingCarrierKeyRecipeBlocks with
  | nil => exact List.Forall₂.nil
  | cons block blocks induction =>
      exact List.Forall₂.cons (by simp) induction

/-- On a tagged descriptor-slot pair, compiled recipe activations are
exactly the activations obtained by repeating each slot bit across its
explicit axis block. -/
theorem crossingCarrierKeyExpandedActives_eq_axisBlockActives
    (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingCarrierKeyExpandedActives
        (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
          pair) =
      FixedAxisUnaryFields.blockActives
        (crossingActivations
          (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
            pair))
        crossingCarrierKeyRecipeAxisBlocks := by
  rw [crossingCarrierKeyExpandedActives_descriptorSlotPairTokens]
  exact expandedActives_eq_axisBlockActives_of_forall₂_length
    (crossingActivations
      (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
        pair))
    crossingCarrierKeyRecipeBlocks_forall₂_axisBlocks_length

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
