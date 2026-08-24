/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotExpansionCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Semantic compiler for fixed occurrence-slot word expansion -/

noncomputable section

namespace LeanTrominoes
namespace DelimitedBinaryWordOccurrenceSlotTags

open Computability Turing

/-- The physical slot expander, retyped as the semantic transformation from
one delimited-word input to its eighty-one-copy expansion. -/
noncomputable def expandInputComputableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode expandInput :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    inputTokensComputableInPolyTime fun input => by
      exact tokens_encode input

end DelimitedBinaryWordOccurrenceSlotTags
end LeanTrominoes

end
