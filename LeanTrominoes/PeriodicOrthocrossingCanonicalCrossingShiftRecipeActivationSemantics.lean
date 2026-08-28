/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftRecipeActivationCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingTruthListSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationLength

/-! # Semantics of common-shift crossing recipe activations -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

@[simp] theorem canonicalCrossingShiftLeftSourceKeyExpandedActives_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    canonicalCrossingShiftLeftSourceKeyExpandedActives
        (descriptorSlotPairTokens pair) =
      expandedActives
        (canonicalCrossingShiftSlots.map fun slot =>
          slot.evalTokens (descriptorSlotPairTokens pair))
        canonicalCrossingShiftLeftSourceKeyRecipeBlocks := by
  unfold canonicalCrossingShiftLeftSourceKeyExpandedActives
  rw [truthValuesFor_descriptorSlotPairTokens]
  apply compiledExpandedActives_eq
  simp [canonicalCrossingShiftLeftSourceKeyRecipeBlocks]

@[simp] theorem canonicalCrossingShiftLeftSourceKeyExpandedActives_length
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (canonicalCrossingShiftLeftSourceKeyExpandedActives
      (descriptorSlotPairTokens pair)).length =
        canonicalCrossingShiftLeftSourceKeyRecipeBlocks.flatten.length := by
  rw [canonicalCrossingShiftLeftSourceKeyExpandedActives_descriptorSlotPairTokens]
  exact expandedActives_length_of_length_eq _ _ (by
    simp [canonicalCrossingShiftLeftSourceKeyRecipeBlocks])

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
