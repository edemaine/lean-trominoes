/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity

/-! # A finite encoding of binary-word pairs -/

namespace LeanTrominoes
namespace DelimitedBinaryWordPairs

/-- Finite physical alphabet for a sequence of binary-word pairs. -/
inductive Token
  | pairStart
  | firstBit (value : Bool)
  | middle
  | secondBit (value : Bool)
  | pairEnd
  deriving DecidableEq, Fintype, Inhabited

/-- Semantic input packaged separately from its delimiter encoding. -/
structure Input where
  pairs : List (List Bool × List Bool)
  deriving DecidableEq

def pairTokens (pair : List Bool × List Bool) : List Token :=
  .pairStart ::
    (pair.1.map .firstBit ++
      .middle :: (pair.2.map .secondBit ++ [.pairEnd]))

def encode (input : Input) : List Token :=
  input.pairs.flatMap pairTokens

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

theorem parse_append (state : ParseState) (first second : List Token) :
    parse state (first ++ second) = parse (parse state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons token first induction =>
      simp only [List.cons_append, parse]
      exact induction (parseStep state token)

theorem parse_firstBits (pairs : List (List Bool × List Bool))
    (first firstReverse : List Bool) :
    parse (.first pairs firstReverse) (first.map .firstBit) =
      .first pairs (first.reverse ++ firstReverse) := by
  induction first generalizing firstReverse with
  | nil => simp [parse]
  | cons bit first induction =>
      simp only [List.map_cons, parse, parseStep]
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

theorem parse_secondBits (pairs : List (List Bool × List Bool))
    (first second secondReverse : List Bool) :
    parse (.second pairs first secondReverse) (second.map .secondBit) =
      .second pairs first (second.reverse ++ secondReverse) := by
  induction second generalizing secondReverse with
  | nil => simp [parse]
  | cons bit second induction =>
      simp only [List.map_cons, parse, parseStep]
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

theorem parse_pairTokens (pairs : List (List Bool × List Bool))
    (pair : List Bool × List Bool) :
    parse (.between pairs) (pairTokens pair) =
      .between (pair :: pairs) := by
  rcases pair with ⟨first, second⟩
  simp only [pairTokens, parse, parseStep]
  rw [parse_append, parse_firstBits]
  simp only [parse, parseStep]
  rw [parse_append, parse_secondBits]
  simp [parse, parseStep]

theorem parse_encodeAux (prior suffix : List (List Bool × List Bool)) :
    parse (.between prior) (suffix.flatMap pairTokens) =
      .between (suffix.reverse ++ prior) := by
  induction suffix generalizing prior with
  | nil => simp [parse]
  | cons pair suffix induction =>
      rw [List.flatMap_cons]
      rw [parse_append, parse_pairTokens]
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem decode_encode (input : Input) :
    decode (encode input) = some input := by
  rcases input with ⟨pairs⟩
  simp [decode, encode, parse_encodeAux]

/-- Physical finite encoding used by the equality machine. -/
noncomputable def finEncoding :
    _root_.Computability.FinEncoding Input where
  toEncoding :=
    { Γ := Token
      encode := encode
      decode := decode
      decode_encode := decode_encode }
  ΓFin := inferInstance

/-- One semantic equality bit per encoded pair. -/
def equalities (input : Input) : List Bool :=
  input.pairs.map fun pair => decide (pair.1 = pair.2)

end DelimitedBinaryWordPairs
end LeanTrominoes
