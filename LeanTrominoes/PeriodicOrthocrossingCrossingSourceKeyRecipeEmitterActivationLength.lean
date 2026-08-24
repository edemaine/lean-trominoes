/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeActivationSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeLength
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationLength

/-! # Activation length of crossing source-key recipe emission -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingSourceKeyRecipeEmitter

open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

@[simp] theorem expandedActives_length_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (RouteDescriptorOccurrenceSlotCrossing.crossingSourceKeyExpandedActives
      (descriptorSlotPairTokens pair)).length = recipes.length := by
  rw [RouteDescriptorOccurrenceSlotCrossing.crossingSourceKeyExpandedActives_descriptorSlotPairTokens]
  unfold recipes
  exact expandedActives_length_of_length_eq _ _
    (RouteDescriptorOccurrenceSlotCrossing.crossingSourceKeyRecipeBlocks_length pair)

end CrossingSourceKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
