/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateWordData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamOutputSemantics
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ListAppendFixedCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Rejection-sentinel completion of the carrier-key word stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeStream

open Computability Turing

def outputWithSentinel (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨(output input).words ++ [PaddedSupportedCandidateWords.sentinelWord]⟩

@[simp] theorem outputWithSentinel_descriptorWords
    (descriptors : List RouteDescriptor) :
    outputWithSentinel (RouteDescriptorBinaryWords.words descriptors) =
      PaddedSupportedCandidateWords.wordsWithSentinel CarrierKeyWords.word
        (paddedCarrierKeyCandidateStream descriptors) := by
  unfold outputWithSentinel
    PaddedSupportedCandidateWords.wordsWithSentinel
  rw [output_descriptorWords, guardedWords_eq_paddedCandidateStream]

theorem appendedTokens_eq_encode_outputWithSentinel
    (input : DelimitedBinaryWords.Input) :
    TM2ListAppend.appendFixedWords
        (DelimitedBinaryWords.wordTokens
          PaddedSupportedCandidateWords.sentinelWord)
        (emittedTokens input) =
      DelimitedBinaryWords.encode (outputWithSentinel input) := by
  rw [emittedTokens_eq_encode_output]
  simp [TM2ListAppend.appendFixedWords, outputWithSentinel,
    DelimitedBinaryWords.encode, List.flatMap_append]

noncomputable def outputWithSentinelComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode outputWithSentinel := by
  let appended := TM2CompositionMachine.computableInPolyTime
    emittedTokensComputableInPolyTime
    (TM2ListAppend.appendFixedComputableInPolyTime
      (DelimitedBinaryWords.wordTokens
        PaddedSupportedCandidateWords.sentinelWord))
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq appended
    appendedTokens_eq_encode_outputWithSentinel

end CarrierKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing

end
