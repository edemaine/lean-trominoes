/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairFourWordExpansionCompiler
import LeanTrominoes.DelimitedBinaryWordPairFourWordExpansionSemantics
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Typed compiler for four-word expansion of binary-word pairs -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordPairFourWordExpansion

open Computability Turing

/-- The semantic four-word expansion is polynomial-time computable under
the canonical pair and word encodings. -/
noncomputable def expandedInputComputableInPolyTime :
    @TM2ComputableInPolyTime
      DelimitedBinaryWordPairs.Input DelimitedBinaryWords.Input
      DelimitedBinaryWordPairs.Token DelimitedBinaryWords.Token
      DelimitedBinaryWordPairs.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode expandedInput := by
  let physical : TM2ComputableInPolyTime
      DelimitedBinaryWordPairs.finEncoding.encode id
      (fun input => tokens
        (DelimitedBinaryWordPairs.finEncoding.encode input)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      DelimitedBinaryWordPairs.finEncoding.encode
      tokensComputableInPolyTime (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    physical fun input => by
      rw [DelimitedBinaryWordPairs.finEncoding_encode, tokens_encode]
      exact (DelimitedBinaryWords.finEncoding_encode _).symm

end LeanTrominoes.DelimitedBinaryWordPairFourWordExpansion

end
