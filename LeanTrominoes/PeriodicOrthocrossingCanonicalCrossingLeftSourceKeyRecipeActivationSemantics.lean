/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingLeftSourceKeyRecipeActivationCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationLength

/-! # Semantics of canonical-left crossing recipe activations -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

@[simp] theorem canonicalLeftSourceKeyExpandedActives_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    canonicalLeftSourceKeyExpandedActives (descriptorSlotPairTokens pair) =
      expandedActives
        (crossingActivations (descriptorSlotPairTokens pair))
        canonicalLeftSourceKeyRecipeBlocks := by
  unfold canonicalLeftSourceKeyExpandedActives compiledRecipeExpandedActives
  rw [truthValues_descriptorSlotPairTokens]
  apply compiledExpandedActives_eq
  simp [crossingActivations, canonicalLeftSourceKeyRecipeBlocks]

@[simp] theorem canonicalLeftSourceKeyExpandedActives_length
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (canonicalLeftSourceKeyExpandedActives
      (descriptorSlotPairTokens pair)).length =
      canonicalLeftSourceKeyRecipeBlocks.flatten.length := by
  rw [canonicalLeftSourceKeyExpandedActives_descriptorSlotPairTokens]
  exact expandedActives_length_of_length_eq _ _ (by
    simp [crossingActivations, canonicalLeftSourceKeyRecipeBlocks])

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
