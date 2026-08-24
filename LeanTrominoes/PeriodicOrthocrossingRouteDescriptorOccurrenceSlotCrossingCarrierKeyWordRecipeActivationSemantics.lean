/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeActivationCompiler

/-! # Semantics of compiled crossing carrier-key recipe activations -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- On canonical tagged descriptor-slot pairs, compiled crossing activation
bits are exactly the semantic flattened recipe activations. -/
@[simp] theorem crossingCarrierKeyExpandedActives_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingCarrierKeyExpandedActives (descriptorSlotPairTokens pair) =
      expandedActives
        (crossingActivations (descriptorSlotPairTokens pair))
        crossingCarrierKeyRecipeBlocks := by
  unfold crossingCarrierKeyExpandedActives compiledRecipeExpandedActives
  rw [truthValues_descriptorSlotPairTokens]
  apply compiledExpandedActives_eq
  simp [crossingActivations, crossingCarrierKeyRecipeBlocks]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
