/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyGuardedWordData

/-! # Semantic crossing source-key guarded-word streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingSourceKeyRecipeStream

open RouteDescriptorOccurrenceSlotBinaryWords

def guardedWords (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    List (List Bool) :=
  pairs.flatMap fun pair =>
    RouteDescriptorOccurrenceSlotCrossing.crossingSourceKeyGuardedWords
      (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens pair)

end CrossingSourceKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing
