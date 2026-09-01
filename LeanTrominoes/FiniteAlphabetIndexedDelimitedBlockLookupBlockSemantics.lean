/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookupSemantics
import LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookupBlockSemantics

/-! # Blockwise semantics of indexed delimited lookup -/

namespace LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookup

open FiniteAlphabetDelimitedBlockJoin

variable {Alphabet : Type}

/-- Broadcasting the consecutive body ordinals across complete delimited
bodies recovers the delimiter-derived physical ordinal of every token. -/
theorem broadcastRange_blocks (bodies : List (List Alphabet)) :
    FiniteAlphabetKeyedDelimitedBlockLookup.broadcastKeys
        (List.range bodies.length) (blocks bodies) =
      candidateKeys (blocks bodies) := by
  unfold FiniteAlphabetKeyedDelimitedBlockLookup.broadcastKeys
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt]
  · have mapped :
        (candidateKeys (blocks bodies)).map
            (fun query => (List.range bodies.length).getD query 0) =
          (candidateKeys (blocks bodies)).map id := by
      apply List.map_congr_left
      intro query member
      have queryLt : query < bodies.length := by
        rw [FiniteAlphabetKeyedDelimitedBlockLookup.candidateKeys_blocks]
          at member
        exact FiniteBlockIndices.mem_indices_lt_length
          FiniteAlphabetKeyedDelimitedBlockLookup.delimitedBlockLength
          bodies query member
      rw [List.getD_eq_getElem _ _ (by simpa using queryLt)]
      simp
    simpa using mapped
  · intro query member
    rw [FiniteAlphabetKeyedDelimitedBlockLookup.candidateKeys_blocks]
      at member
    simpa using FiniteBlockIndices.mem_indices_lt_length
      FiniteAlphabetKeyedDelimitedBlockLookup.delimitedBlockLength
      bodies query member

/-- Indexed token lookup is the special case of keyed block lookup whose
aligned body keys are the consecutive zero-based ordinals. -/
theorem selected_blocks
    [Fintype Alphabet]
    (queries : List Nat) (bodies : List (List Alphabet)) :
    selected queries (blocks bodies) =
      FiniteAlphabetKeyedDelimitedBlockLookup.expectedBlocks
        queries (List.range bodies.length) bodies := by
  unfold selected
  rw [← broadcastRange_blocks bodies]
  exact FiniteAlphabetKeyedDelimitedBlockLookup.selected_blocks
    queries (List.range bodies.length) bodies (by simp)

end LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookup
