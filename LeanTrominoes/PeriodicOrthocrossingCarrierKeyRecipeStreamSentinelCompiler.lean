/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamOutput
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ListAppendFixedCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Rejection-sentinel completion of the carrier-key word stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeStream

open Computability Turing

def rejectionSentinel : List Bool := [false]

def outputWithSentinel (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨(output input).words ++ [rejectionSentinel]⟩

theorem appendedTokens_eq_encode_outputWithSentinel
    (input : DelimitedBinaryWords.Input) :
    TM2ListAppend.appendFixedWords
        (DelimitedBinaryWords.wordTokens
          rejectionSentinel)
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
        rejectionSentinel))
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq appended
    appendedTokens_eq_encode_outputWithSentinel

end CarrierKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing

end
