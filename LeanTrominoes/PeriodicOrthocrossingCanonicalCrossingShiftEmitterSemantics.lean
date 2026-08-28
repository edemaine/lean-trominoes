/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeOutputSemantics
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftRecipeEmitterSemantics

/-! # Semantics of merged common-shift canonical-left source keys -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyEmitter

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

@[simp] theorem emittedTokens_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    emittedTokens (descriptorSlotPairTokens pair) =
      DelimitedBinaryWords.encode
        ⟨DelimitedBinaryWordGuardedPairMerge.mergeWords
          (RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyGuardedWords
            (descriptorSlotPairTokens pair))⟩ := by
  unfold emittedTokens
  rw [CanonicalCrossingShiftLeftSourceKeyRecipeEmitter.emittedTokens_descriptorSlotPairTokens,
    DelimitedBinaryWordGuardedPairMerge.tokens_encode_words]

/-- The physical inner compiler emits one guarded word for every fixed
common-shift crossing candidate slot. -/
@[simp] theorem emittedTokens_eq_candidates
    (pair : TaggedDescriptor × TaggedDescriptor) :
    emittedTokens (descriptorSlotPairTokens pair) =
      DelimitedBinaryWords.encode
        ⟨(RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyCandidates
          pair).map
            (PaddedSupportedCandidateWords.guardedWord
              CarrierNodeSourceKeys.word)⟩ := by
  rw [emittedTokens_descriptorSlotPairTokens,
    RouteDescriptorOccurrenceSlotCrossing.mergeWords_canonicalCrossingShiftLeftSourceKeyGuardedWords]

end CanonicalCrossingShiftLeftSourceKeyEmitter
end LeanTrominoes.PeriodicOrthocrossing
