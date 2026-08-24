/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingActiveCarrierKeyRecipeEmitterSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingActiveCarrierKeyRecipeStreamCompiler

/-! # Semantics of activity-supported crossing key streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingActiveCarrierKeyRecipeStream

open RouteDescriptorOccurrenceSlotBinaryWords

def guardedWords (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    List (List Bool) :=
  pairs.flatMap fun pair =>
    RouteDescriptorOccurrenceSlotCrossing.crossingActiveCarrierKeyGuardedWords
      (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens pair)

@[simp] theorem emittedStream_encodeDescriptorSlotPairs
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    emittedStream
        (RouteDescriptorOccurrenceSlotPairFieldTags.encodeDescriptorSlotPairs
          pairs) =
      DelimitedBinaryWords.encode ⟨guardedWords pairs⟩ := by
  unfold emittedStream
  rw [RouteDescriptorOccurrenceSlotPairFieldTags.mappedOutput_encodeDescriptorSlotPairs]
  simp only [CrossingActiveCarrierKeyRecipeEmitter.emittedTokens_descriptorSlotPairTokens]
  unfold guardedWords DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]

end CrossingActiveCarrierKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing
