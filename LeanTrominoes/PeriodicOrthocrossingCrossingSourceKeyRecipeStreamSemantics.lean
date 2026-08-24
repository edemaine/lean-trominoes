/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeEmitterTokenSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeStreamData

/-! # Semantics of crossing source-key guarded-word streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingSourceKeyRecipeStream

open RouteDescriptorOccurrenceSlotBinaryWords

/-- Mapping the crossing source-key block compiler over canonical tagged slot
pairs emits exactly the encoding of their concatenated guarded words. -/
@[simp] theorem emittedStream_encodeDescriptorSlotPairs
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    emittedStream
        (RouteDescriptorOccurrenceSlotPairFieldTags.encodeDescriptorSlotPairs
          pairs) =
      DelimitedBinaryWords.encode ⟨guardedWords pairs⟩ := by
  unfold emittedStream
  rw [RouteDescriptorOccurrenceSlotPairFieldTags.mappedOutput_encodeDescriptorSlotPairs]
  simp only [CrossingSourceKeyRecipeEmitter.emittedTokens_descriptorSlotPairTokens]
  unfold guardedWords DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]

end CrossingSourceKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing
