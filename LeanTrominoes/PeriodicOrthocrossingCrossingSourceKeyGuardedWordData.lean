/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingSourceKeyRecipeData

/-! # Semantic crossing source-key guarded words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

/-- Doubled guarded source-key components for every padded crossing slot. -/
def crossingSourceKeyGuardedWords
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List (List Bool) :=
  RouteDescriptorPairCarrierKeyWordRecipes.words
    (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokens tokens)
    (crossingActivations tokens) crossingSourceKeyRecipeBlocks

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
