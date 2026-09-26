/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookupBlockSemantics

/-! # Indexed block selection is ordinary list lookup -/
namespace LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookup
open FiniteAlphabetDelimitedBlockJoin FiniteAlphabetKeyedDelimitedBlockLookup

theorem selected_blocks_getD {Alphabet : Type} [Fintype Alphabet]
    (queries : List Nat) (bodies : List (List Alphabet))
    (valid : ∀ i ∈ queries, i < bodies.length) :
    selected queries (blocks bodies) = blocks (queries.map (fun i => bodies.getD i [])) := by
  rw [selected_blocks, expectedBlocks_eq_blocks, expectedBodyList_eq_map_alignedBody
    queries (List.range bodies.length) bodies (by simp) List.nodup_range
    (fun i hi => List.mem_range.mpr (valid i hi))]
  congr 1
  apply List.map_congr_left
  intro i hi
  have idx : (List.range bodies.length).idxOf i = i := by
    have h := (List.nodup_range (n := bodies.length)).idxOf_getElem i (by simpa using valid i hi)
    rw [List.getElem_range] at h
    exact h
  simp only [alignedBody, idx]

end LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookup
