/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookupCompiler
import LeanTrominoes.FiniteAlphabetKeyedValueLookupSemantics

/-! # Semantics of indexed finite-alphabet delimited-block lookup -/

noncomputable section

namespace LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookup

variable {Alphabet : Type} [Fintype Alphabet]

/-- The compiled lookup is exactly query-major selection of all tokens whose
broadcast block ordinal equals the current query. -/
@[simp] theorem selected_eq_expected
    (queries : List Nat) (tokens : List (Token Alphabet)) :
    selected queries tokens = expected queries tokens := by
  unfold selected expected
  exact FiniteAlphabetKeyedValueLookup.values_eq_expected
    queries (candidateKeys tokens) tokens (candidateKeys_length tokens)

end LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookup

end
