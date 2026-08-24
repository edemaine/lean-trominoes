/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeActivationCompiler

/-! # Semantics of compiled crossing source-key recipe activations -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- On canonical tagged descriptor-slot pairs, compiled crossing source-key
activation bits are exactly the semantic flattened recipe activations. -/
@[simp] theorem crossingSourceKeyExpandedActives_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingSourceKeyExpandedActives (descriptorSlotPairTokens pair) =
      expandedActives
        (crossingActivations (descriptorSlotPairTokens pair))
        crossingSourceKeyRecipeBlocks := by
  unfold crossingSourceKeyExpandedActives compiledRecipeExpandedActives
  rw [truthValues_descriptorSlotPairTokens]
  apply compiledExpandedActives_eq
  simp [crossingActivations, crossingSourceKeyRecipeBlocks]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
