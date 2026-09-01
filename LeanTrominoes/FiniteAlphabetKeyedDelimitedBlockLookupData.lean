/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookupData
import LeanTrominoes.UnaryIndexedValueLookupSemantics

/-! # Arbitrarily keyed finite-alphabet delimited blocks -/

namespace LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookup

abbrev Token (Alphabet : Type) :=
  FiniteAlphabetIndexedDelimitedBlockLookup.Token Alphabet

/-- Broadcast every supplied block key across the tokens carrying that
block's zero-based ordinal. -/
def broadcastKeys {Alphabet : Type}
    (blockKeys : List Nat) (tokens : List (Token Alphabet)) : List Nat :=
  UnaryIndexedValueLookup.values
    (FiniteAlphabetIndexedDelimitedBlockLookup.candidateKeys tokens)
    blockKeys

/-- Select complete keyed blocks in arbitrary query order. -/
noncomputable def selected {Alphabet : Type} [Fintype Alphabet]
    (queries blockKeys : List Nat)
    (tokens : List (Token Alphabet)) : List (Token Alphabet) :=
  FiniteAlphabetKeyedValueLookup.values
    queries (broadcastKeys blockKeys tokens) tokens

/-- Direct relational specification of the token-level keyed lookup. -/
def expected {Alphabet : Type}
    (queries blockKeys : List Nat)
    (tokens : List (Token Alphabet)) : List (Token Alphabet) :=
  FiniteAlphabetKeyedValueLookup.expected
    queries (broadcastKeys blockKeys tokens) tokens

@[simp] theorem broadcastKeys_length {Alphabet : Type}
    (blockKeys : List Nat) (tokens : List (Token Alphabet)) :
    (broadcastKeys blockKeys tokens).length = tokens.length := by
  unfold broadcastKeys
  rw [UnaryIndexedValueLookup.values_length,
    FiniteAlphabetIndexedDelimitedBlockLookup.candidateKeys_length]

end LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookup
