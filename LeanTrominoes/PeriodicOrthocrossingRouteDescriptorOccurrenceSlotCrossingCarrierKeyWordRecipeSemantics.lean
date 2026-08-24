/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeyWordRecipeBlockSemantics

/-! # Semantics of the complete slot-major crossing recipe family -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairAffine
open RouteDescriptorPairCarrierKeyWordRecipes

/-- Interpreting one crossing slot's recipes gives its existing semantic
carrier-key template block. -/
@[simp] theorem Slot.map_template_carrierKeyRecipeBlock
    (slot : Slot) (pair : RouteDescriptor × RouteDescriptor) :
    slot.carrierKeyRecipeBlock.map (Recipe.template pair) =
      slot.carrierKeyTemplateBlock pair := by
  unfold Slot.carrierKeyRecipeBlock Slot.carrierKeyTemplateBlock
  exact map_template_occurrencePairCrossingCarrierKeyRecipeBlock
    pair slot.occurrences

/-- Interpreting the complete slot-major recipe family gives the existing
complete crossing template family. -/
@[simp] theorem map_map_template_crossingCarrierKeyRecipeBlocks
    (pair : RouteDescriptor × RouteDescriptor) :
    crossingCarrierKeyRecipeBlocks.map
        (fun block => block.map (Recipe.template pair)) =
      crossingCarrierKeyTemplateBlocks pair := by
  unfold crossingCarrierKeyRecipeBlocks crossingCarrierKeyTemplateBlocks
  rw [List.map_map]
  apply List.map_congr_left
  intro slot _slotMember
  exact slot.map_template_carrierKeyRecipeBlock pair

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
