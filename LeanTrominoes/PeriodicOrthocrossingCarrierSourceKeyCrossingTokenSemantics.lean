/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyCrossingTagSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeStreamSemantics

/-! # Canonical crossing tokens of the source-key component stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyComponentStream

open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem crossingTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    crossingTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨CrossingSourceKeyRecipeStream.guardedWords
          (taggedDescriptors descriptors ×ˢ
            taggedDescriptors descriptors)⟩ := by
  unfold crossingTokens
  rw [crossingTags_descriptorWords,
    CrossingSourceKeyRecipeStream.emittedStream_encodeDescriptorSlotPairs]

end CarrierSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing
