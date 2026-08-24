/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeTemplateSemantics

/-! # Crossing carrier-key recipe block semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairFieldTags

/-- Interpreting one shifted occurrence recipe gives the corresponding
semantic carrier-key template. -/
@[simp] theorem Occurrence.template_carrierKeyRecipeAtShift
    (occurrence : Occurrence) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) (shift : Cell) :
    (occurrence.carrierKeyRecipeAtShift side shift).template pair =
      (⟨occurrence.carrierKeyAtShift side pair shift,
        occurrence.carrierKeyAtShiftSupported shift⟩ :
        Template CarrierKeyWords.CarrierKey) := by
  cases side <;>
    rfl

/-- Interpreting the four recipes of one retained shift gives its existing
four crossing carrier-key templates. -/
@[simp] theorem map_template_occurrencePairCrossingCarrierKeyShiftRecipeBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) (shift : Cell) :
    (occurrencePairCrossingCarrierKeyShiftRecipeBlock
        occurrences shift).map (Recipe.template pair) =
      occurrencePairCrossingCarrierKeyShiftTemplateBlock
        pair occurrences shift := by
  simp [occurrencePairCrossingCarrierKeyShiftRecipeBlock,
    occurrencePairCrossingCarrierKeyShiftTemplateBlock]

/-- The complete retained-shift recipe family of one occurrence pair
interprets to its complete semantic template family. -/
@[simp] theorem map_template_occurrencePairCrossingCarrierKeyRecipeBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) :
    (occurrencePairCrossingCarrierKeyRecipeBlock occurrences).map
        (Recipe.template pair) =
      occurrencePairCrossingCarrierKeyTemplateBlock pair occurrences := by
  unfold occurrencePairCrossingCarrierKeyRecipeBlock
    occurrencePairCrossingCarrierKeyTemplateBlock
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro shift _shiftMember
  exact map_template_occurrencePairCrossingCarrierKeyShiftRecipeBlock
    pair occurrences shift

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
