/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyMergedDescriptorOutputData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierSourceKeyCandidateStreamData
import LeanTrominoes.TM2ListAppendFixedCompiler

/-! # Rejection-sentinel completion of merged carrier source keys -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedCandidateWords

theorem appendedSourceKeySentinelTokens_eq
    (descriptors : List RouteDescriptor) :
    TM2ListAppend.appendFixedWords
        (DelimitedBinaryWords.wordTokens sentinelWord)
        (DelimitedBinaryWords.encode
          (CarrierSourceKeyMergedStream.descriptorOutput descriptors)) =
      DelimitedBinaryWords.encode
        (paddedCarrierSourceKeyWordsWithSentinel descriptors) := by
  unfold CarrierSourceKeyMergedStream.descriptorOutput
    CarrierNodeSourceKeyCandidateWords.mergedWords
    paddedCarrierSourceKeyWordsWithSentinel
    paddedCarrierSourceKeyCandidateStream wordsWithSentinel
    TM2ListAppend.appendFixedWords DelimitedBinaryWords.encode
  simp [List.map_map, List.flatMap_append, Function.comp_def]

end LeanTrominoes.PeriodicOrthocrossing
