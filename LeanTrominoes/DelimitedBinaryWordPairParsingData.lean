/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairData

/-! # Parsing data for delimiter-encoded binary-word pairs -/

namespace LeanTrominoes.DelimitedBinaryWordPairs

/-- Decoder state; partial fields are kept reversed while scanning. -/
inductive ParseState
  | between (pairsReverse : List (List Bool × List Bool))
  | first (pairsReverse : List (List Bool × List Bool))
      (firstReverse : List Bool)
  | second (pairsReverse : List (List Bool × List Bool))
      (first : List Bool) (secondReverse : List Bool)
  | invalid

def parseStep : ParseState → Token → ParseState
  | .between pairs, .pairStart => .first pairs []
  | .first pairs first, .firstBit bit => .first pairs (bit :: first)
  | .first pairs first, .middle => .second pairs first.reverse []
  | .second pairs first second, .secondBit bit =>
      .second pairs first (bit :: second)
  | .second pairs first second, .pairEnd =>
      .between ((first, second.reverse) :: pairs)
  | _, _ => .invalid

def parse : ParseState → List Token → ParseState
  | state, [] => state
  | state, token :: tokens => parse (parseStep state token) tokens

def decode (tokens : List Token) : Option Input :=
  match parse (.between []) tokens with
  | .between pairsReverse => some ⟨pairsReverse.reverse⟩
  | _ => none

end LeanTrominoes.DelimitedBinaryWordPairs
