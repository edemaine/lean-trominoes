/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinData
import LeanTrominoes.FiniteAlphabetKeyedValueLookupData
import LeanTrominoes.PrefixSums

/-! # Indexed lookup of finite-alphabet delimited blocks -/

noncomputable section

namespace LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookup

abbrev Token (Alphabet : Type) :=
  FiniteAlphabetDelimitedBlockJoin.Token Alphabet

/-- Advance the block ordinal immediately after a block delimiter. -/
def increment {Alphabet : Type} : Token Alphabet → Nat
  | .value _ => 0
  | .blockEnd => 1

def increments {Alphabet : Type} (tokens : List (Token Alphabet)) :
    List Nat :=
  tokens.map increment

/-- The zero-based ordinal of the block containing each token.  In
particular, a delimiter receives the same key as the body it terminates. -/
def candidateKeys {Alphabet : Type} (tokens : List (Token Alphabet)) :
    List Nat :=
  PrefixSums.starts (increments tokens)

/-- Select every token in each queried block, retaining its delimiter. -/
def selected {Alphabet : Type} [Fintype Alphabet]
    (queries : List Nat) (tokens : List (Token Alphabet)) :
    List (Token Alphabet) :=
  FiniteAlphabetKeyedValueLookup.values
    queries (candidateKeys tokens) tokens

/-- Direct relational specification used by the generic keyed selector. -/
def expected {Alphabet : Type}
    (queries : List Nat) (tokens : List (Token Alphabet)) :
    List (Token Alphabet) :=
  FiniteAlphabetKeyedValueLookup.expected
    queries (candidateKeys tokens) tokens

@[simp] theorem increments_length {Alphabet : Type}
    (tokens : List (Token Alphabet)) :
    (increments tokens).length = tokens.length := by
  simp [increments]

@[simp] theorem candidateKeys_length {Alphabet : Type}
    (tokens : List (Token Alphabet)) :
    (candidateKeys tokens).length = tokens.length := by
  simp [candidateKeys]

end LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookup

end
