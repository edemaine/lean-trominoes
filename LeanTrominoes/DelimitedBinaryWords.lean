/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity

/-! # A finite encoding of lists of binary words -/

namespace LeanTrominoes
namespace DelimitedBinaryWords

/-- Finite physical alphabet for delimiter-separated binary words. -/
inductive Token
  | wordStart
  | bit (value : Bool)
  | wordEnd
  deriving DecidableEq, Fintype, Inhabited

structure Input where
  words : List (List Bool)
  deriving DecidableEq

def wordTokens (word : List Bool) : List Token :=
  .wordStart :: (word.map .bit ++ [.wordEnd])

def encode (input : Input) : List Token :=
  input.words.flatMap wordTokens

inductive ParseState
  | between (wordsReverse : List (List Bool))
  | word (wordsReverse : List (List Bool)) (bitsReverse : List Bool)
  | invalid

def parseStep : ParseState → Token → ParseState
  | .between words, .wordStart => .word words []
  | .word words bits, .bit value => .word words (value :: bits)
  | .word words bits, .wordEnd => .between (bits.reverse :: words)
  | _, _ => .invalid

def parse : ParseState → List Token → ParseState
  | state, [] => state
  | state, token :: tokens => parse (parseStep state token) tokens

def decode (tokens : List Token) : Option Input :=
  match parse (.between []) tokens with
  | .between wordsReverse => some ⟨wordsReverse.reverse⟩
  | _ => none

theorem parse_append (state : ParseState) (first second : List Token) :
    parse state (first ++ second) = parse (parse state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons token first induction =>
      simp only [List.cons_append, parse]
      exact induction (parseStep state token)

theorem parse_bits (words : List (List Bool))
    (bits bitsReverse : List Bool) :
    parse (.word words bitsReverse) (bits.map .bit) =
      .word words (bits.reverse ++ bitsReverse) := by
  induction bits generalizing bitsReverse with
  | nil => simp [parse]
  | cons bit bits induction =>
      simp only [List.map_cons, parse, parseStep]
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

theorem parse_wordTokens (words : List (List Bool)) (word : List Bool) :
    parse (.between words) (wordTokens word) =
      .between (word :: words) := by
  simp only [wordTokens, parse, parseStep]
  rw [parse_append, parse_bits]
  simp [parse, parseStep]

theorem parse_encodeAux (prior suffix : List (List Bool)) :
    parse (.between prior) (suffix.flatMap wordTokens) =
      .between (suffix.reverse ++ prior) := by
  induction suffix generalizing prior with
  | nil => simp [parse]
  | cons word suffix induction =>
      rw [List.flatMap_cons, parse_append, parse_wordTokens,
        induction]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem decode_encode (input : Input) :
    decode (encode input) = some input := by
  rcases input with ⟨words⟩
  simp [decode, encode, parse_encodeAux]

noncomputable def finEncoding :
    _root_.Computability.FinEncoding Input where
  toEncoding :=
    { Γ := Token
      encode := encode
      decode := decode
      decode_encode := decode_encode }
  ΓFin := inferInstance

end DelimitedBinaryWords
end LeanTrominoes
