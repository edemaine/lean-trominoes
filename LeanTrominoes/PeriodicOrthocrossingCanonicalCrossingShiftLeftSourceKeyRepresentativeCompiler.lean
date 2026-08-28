/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyRepresentativeData
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyStreamSemantics
import LeanTrominoes.TM2ListAppendFixedCompiler
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for common-shift source-key representatives -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyRepresentatives

open Computability Turing
open PaddedSupportedCandidateWords

abbrev descriptorInputEncoding :
    List RouteDescriptor → List DelimitedBinaryWords.Token :=
  fun descriptors =>
    DelimitedBinaryWords.encode
      (RouteDescriptorBinaryWords.words descriptors)

/-- Append the fixed rejection sentinel to the guarded candidate stream. -/
def emittedTokensWithSentinel (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  CanonicalCrossingShiftLeftSourceKeyStream.emittedDescriptorStream input ++
    DelimitedBinaryWords.wordTokens sentinelWord

noncomputable def emittedTokensWithSentinelComputableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id
      emittedTokensWithSentinel := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => TM2ListAppend.appendFixedWords
      (DelimitedBinaryWords.wordTokens sentinelWord)
      (CanonicalCrossingShiftLeftSourceKeyStream.emittedDescriptorStream
        input))
  exact TM2CompositionMachine.computableInPolyTime
    CanonicalCrossingShiftLeftSourceKeyStream.emittedDescriptorStreamComputableInPolyTime
    (TM2ListAppend.appendFixedComputableInPolyTime
      (DelimitedBinaryWords.wordTokens sentinelWord))

@[simp] theorem emittedTokensWithSentinel_descriptorWords
    (descriptors : List RouteDescriptor) :
    emittedTokensWithSentinel
        (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode (wordsWithSentinel descriptors) := by
  rw [emittedTokensWithSentinel,
    CanonicalCrossingShiftLeftSourceKeyStream.emittedDescriptorStream_descriptorWords]
  unfold wordsWithSentinel candidateList
    PaddedSupportedCandidateWords.wordsWithSentinel
  rw [CanonicalCrossingShiftLeftSourceKeyStream.guardedWords_eq_candidates]
  simp [DelimitedBinaryWords.encode, List.flatMap_append]

noncomputable def wordsWithSentinelComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding
      DelimitedBinaryWords.finEncoding.encode wordsWithSentinel := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words
    emittedTokensWithSentinelComputableInPolyTime
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared
    emittedTokensWithSentinel_descriptorWords

/-- The generic equality-square and last-representative machines compile the
exact stable source-pair representative rows. -/
noncomputable def representativeRowsComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding
      DelimitedBinaryWords.finEncoding.encode representativeRows :=
  PaddedSupportedCandidateWords.representativeRowsComputableInPolyTime
    descriptorInputEncoding CarrierNodeSourceKeys.word candidateList
    wordsWithSentinelComputableInPolyTime

end CanonicalCrossingShiftLeftSourceKeyRepresentatives
end LeanTrominoes.PeriodicOrthocrossing

end
