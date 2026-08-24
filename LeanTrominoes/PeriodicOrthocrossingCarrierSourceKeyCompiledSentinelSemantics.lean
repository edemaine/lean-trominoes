/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyMergedCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeySentinelSemantics

/-! # Sentinel completion of compiled carrier source-key tokens -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedCandidateWords

theorem appendedCompiledSourceKeySentinelTokens_eq
    (descriptors : List RouteDescriptor) :
    TM2ListAppend.appendFixedWords
        (DelimitedBinaryWords.wordTokens sentinelWord)
        (CarrierSourceKeyMergedStream.tokens
          (RouteDescriptorBinaryWords.words descriptors)) =
      DelimitedBinaryWords.encode
        (paddedCarrierSourceKeyWordsWithSentinel descriptors) := by
  rw [CarrierSourceKeyMergedStream.tokens_descriptorWords]
  exact appendedSourceKeySentinelTokens_eq descriptors

end LeanTrominoes.PeriodicOrthocrossing
