/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyAxisDatum
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeSemantics

/-! # Axis semantics of an inactive crossing slot -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open RouteDescriptorPairCarrierKeyWordRecipes

/-- An inactive crossing slot maps every aligned recipe/template position to
zero, independently of its fixed payload. -/
theorem Slot.carrierKeyAxisTemplate_inactive
    (descriptors : List RouteDescriptor)
    (slot : Slot) (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (fun axis template =>
        FixedAxisUnaryFields.value false axis =
          RouteDescriptorCarrierKeyAxisDatum.value descriptors
            (Template.activate false template).value)
      (slot.carrierKeyRecipeBlock.map fun recipe =>
        decide (recipe.side = .first))
      (slot.carrierKeyTemplateBlock pair) := by
  rw [← slot.map_template_carrierKeyRecipeBlock]
  induction slot.carrierKeyRecipeBlock with
  | nil => exact List.Forall₂.nil
  | cons recipe recipes induction =>
      simp only [List.map_cons]
      exact List.Forall₂.cons
        (by simp [FixedAxisUnaryFields.value, Template.activate,
          RouteDescriptorCarrierKeyAxisDatum.value_none])
        induction

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
