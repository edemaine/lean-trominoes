/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingSourceKeyRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagData

/-! # Length alignment of crossing source-key recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

@[simp] theorem crossingSourceKeyRecipeBlocks_length
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (crossingActivations (descriptorSlotPairTokens pair)).length =
      crossingSourceKeyRecipeBlocks.length := by
  simp [crossingActivations, crossingSourceKeyRecipeBlocks]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
