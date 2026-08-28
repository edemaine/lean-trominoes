/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords

/-! # Total decoding of delimited binary words -/

namespace LeanTrominoes
namespace DelimitedBinaryWords

/-- Decode a token stream, using the empty word list for malformed input. -/
def decodeOrEmpty (tokens : List Token) : Input :=
  match decode tokens with
  | some input => input
  | none => ⟨[]⟩

@[simp] theorem decodeOrEmpty_encode (input : Input) :
    decodeOrEmpty (encode input) = input := by
  simp [decodeOrEmpty]

end DelimitedBinaryWords
end LeanTrominoes
