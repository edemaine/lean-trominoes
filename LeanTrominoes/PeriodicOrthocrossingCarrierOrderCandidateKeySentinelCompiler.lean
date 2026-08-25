/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateKeyStreamSemantics
import LeanTrominoes.TM2ListAppendFixedCompiler
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Sentinel-completed carrier order-coordinate candidate keys -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderCandidateKeyStream

open Computability Turing
open PaddedSupportedCandidateWords

def emittedTokensWithSentinel (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  emittedTokens input ++ DelimitedBinaryWords.wordTokens sentinelWord

def wordsWithSentinel (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  ⟨guardedWords descriptors ++ [sentinelWord]⟩

def emittedTokensWithSentinelComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      emittedTokensWithSentinel := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => TM2ListAppend.appendFixedWords
      (DelimitedBinaryWords.wordTokens sentinelWord)
      (emittedTokens input))
  exact TM2CompositionMachine.computableInPolyTime
    emittedTokensComputableInPolyTime
    (TM2ListAppend.appendFixedComputableInPolyTime
      (DelimitedBinaryWords.wordTokens sentinelWord))

@[simp] theorem emittedTokensWithSentinel_descriptorWords
    (descriptors : List RouteDescriptor) :
    emittedTokensWithSentinel
        (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode (wordsWithSentinel descriptors) := by
  rw [emittedTokensWithSentinel, emittedTokens_descriptorWords]
  simp [wordsWithSentinel, DelimitedBinaryWords.encode,
    List.flatMap_append]

def wordsWithSentinelComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      DelimitedBinaryWords.finEncoding.encode wordsWithSentinel := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words
    emittedTokensWithSentinelComputableInPolyTime
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared
    emittedTokensWithSentinel_descriptorWords

end CarrierOrderCandidateKeyStream
end LeanTrominoes.PeriodicOrthocrossing

end
