/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookupCompiler
import LeanTrominoes.FiniteAlphabetKeyedValueLookupSemantics

/-! # Semantics of arbitrarily keyed delimited-block lookup -/

namespace LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookup

variable {Alphabet : Type} [Fintype Alphabet]

/-- The compiler is exactly query-major token selection at the broadcast
block keys. -/
@[simp] theorem selected_eq_expected
    (queries blockKeys : List Nat) (tokens : List (Token Alphabet)) :
    selected queries blockKeys tokens = expected queries blockKeys tokens := by
  unfold selected expected
  exact FiniteAlphabetKeyedValueLookup.values_eq_expected
    queries (broadcastKeys blockKeys tokens) tokens
      (broadcastKeys_length blockKeys tokens)

end LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookup
