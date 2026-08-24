/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisValueData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyCompiledActivationLength

/-! # Alignment lengths of padded crossing axis values -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem crossingCarrierKeyRecipeAxes_length :
    crossingCarrierKeyRecipeAxes.length =
      crossingCarrierKeyRecipeBlocks.flatten.length := by
  unfold crossingCarrierKeyRecipeAxes
  rw [List.length_map]

@[simp] theorem crossingCarrierKeyRecipeBlocks_length :
    crossingCarrierKeyRecipeBlocks.length = crossingSlots.length := by
  simp [crossingCarrierKeyRecipeBlocks]

@[simp] theorem truthValues_length
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    (truthValues tokens).length = crossingSlots.length := by
  rw [truthValues_eq_zipWith, List.length_zipWith,
    descriptorTruthValues_length, slotGuardTruthValues_length]
  simp

/-- Every runtime crossing activation word aligns with the fixed axis word. -/
theorem crossingCarrierKeyExpandedActives_axis_length
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    (crossingCarrierKeyExpandedActives tokens).length =
      crossingCarrierKeyRecipeAxes.length := by
  change
    (compiledExpandedActives crossingCarrierKeyRecipeBlocks
      (truthValues tokens)).length = crossingCarrierKeyRecipeAxes.length
  calc
    _ = crossingCarrierKeyRecipeBlocks.flatten.length :=
      compiledExpandedActives_length_of_length_eq _ _
        ((truthValues_length tokens).trans
          crossingCarrierKeyRecipeBlocks_length.symm)
    _ = crossingCarrierKeyRecipeAxes.length :=
      crossingCarrierKeyRecipeAxes_length.symm

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
