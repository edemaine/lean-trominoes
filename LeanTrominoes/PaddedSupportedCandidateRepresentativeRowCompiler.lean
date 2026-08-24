/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordRepresentativeSquareCompiler
import LeanTrominoes.DelimitedBinaryWordsDropLastTime
import LeanTrominoes.PaddedSupportedCandidateRepresentativeSquareBridge
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for guarded padded-candidate representative rows -/

noncomputable section

namespace LeanTrominoes.PaddedSupportedCandidateWords

open Computability Turing
open PaddedSupportedLastRepresentativeEqualityRows

/-- Any polynomial-time emitter of guarded candidate words with their final
sentinel composes with the generic square, representative selector, and
drop-last machine to compute the sentinel-free representative rows. -/
noncomputable def representativeRowsComputableInPolyTime
    {Input InputSymbol Value : Type}
    (encodeInput : Input → List InputSymbol)
    (encodeValue : Value → List Bool)
    (candidates : Input → List (Candidate Value))
    (wordCompiler :
      @TM2ComputableInPolyTime
        Input DelimitedBinaryWords.Input
        InputSymbol DelimitedBinaryWords.Token
        encodeInput DelimitedBinaryWords.finEncoding.encode
        (fun input => wordsWithSentinel encodeValue (candidates input))) :
    @TM2ComputableInPolyTime
      Input DelimitedBinaryWords.Input InputSymbol
      DelimitedBinaryWords.Token
      encodeInput DelimitedBinaryWords.finEncoding.encode
      (fun input => representativeRows encodeValue (candidates input)) := by
  let selectedWithSentinel :=
    DelimitedBinaryWordRepresentativeSquare.rowsComputableInPolyTime
      encodeInput
      (fun input => wordsWithSentinel encodeValue (candidates input))
      wordCompiler
  let dropped := TM2CompositionMachine.computableInPolyTime
    selectedWithSentinel
    DelimitedBinaryWordsDropLastMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq dropped
    (fun input => by
      rw [dropLast_representativeSquareRows_eq])

end LeanTrominoes.PaddedSupportedCandidateWords

end
