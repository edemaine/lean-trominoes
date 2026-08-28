/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagData

/-! # Semantic streams of normalized carrier source-key recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRecipeStream

open RouteDescriptorOccurrenceSlotBinaryWords

/-- Normalized terminal candidate words in descriptor-pair order. -/
def terminalGuardedWords
    (pairs : List (RouteDescriptor × RouteDescriptor)) : List (List Bool) :=
  pairs.flatMap fun pair =>
    (CarrierNormalizedSourceKeyRecipes.terminalOutput
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair)).words

/-- Normalized crossing candidate words in tagged descriptor-slot-pair
order. -/
def crossingGuardedWords
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) : List (List Bool) :=
  pairs.flatMap fun pair =>
    (CarrierNormalizedSourceKeyRecipes.crossingOutput
      (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
        pair)).words

end CarrierNormalizedSourceKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing
