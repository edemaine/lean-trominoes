/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookupSemantics
import LeanTrominoes.FiniteBlockIndexLookupSemantics

/-! # Blockwise semantics of keyed delimited lookup -/

namespace LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookup

open FiniteAlphabetDelimitedBlockJoin

variable {Alphabet : Type}

/-- Every abstract body contributes its payload length plus its closing
delimiter to the physical token stream. -/
def delimitedBlockLength (body : List Alphabet) : Nat :=
  body.length + 1

private theorem increments_block (body : List Alphabet) :
    FiniteAlphabetIndexedDelimitedBlockLookup.increments (block body) =
      FiniteBlockIndices.increments delimitedBlockLength [body] := by
  simp [FiniteAlphabetIndexedDelimitedBlockLookup.increments,
    FiniteAlphabetIndexedDelimitedBlockLookup.increment,
    block, FiniteBlockIndices.increments, FiniteBlockIndices.markers,
    FiniteBlockIndices.itemMarkers, FiniteBlockIndices.endingMarkers,
    FiniteUnaryFieldMap.values, delimitedBlockLength, List.map_append,
    Function.comp_def]

/-- The delimiter-based ordinal stream is the ordinary finite-block index
stream for bodies whose physical length includes one closing delimiter. -/
theorem candidateKeys_blocks (bodies : List (List Alphabet)) :
    FiniteAlphabetIndexedDelimitedBlockLookup.candidateKeys
        (blocks bodies) =
      FiniteBlockIndices.indices delimitedBlockLength bodies := by
  unfold FiniteAlphabetIndexedDelimitedBlockLookup.candidateKeys
    FiniteBlockIndices.indices
  congr 1
  induction bodies with
  | nil => rfl
  | cons body bodies induction =>
      rw [show blocks (body :: bodies) = block body ++ blocks bodies by rfl]
      rw [show FiniteAlphabetIndexedDelimitedBlockLookup.increments
              (block body ++ blocks bodies) =
            FiniteAlphabetIndexedDelimitedBlockLookup.increments
                (block body) ++
              FiniteAlphabetIndexedDelimitedBlockLookup.increments
                (blocks bodies) by
        simp [FiniteAlphabetIndexedDelimitedBlockLookup.increments]]
      rw [show FiniteBlockIndices.increments delimitedBlockLength
            (body :: bodies) =
          FiniteBlockIndices.increments delimitedBlockLength [body] ++
            FiniteBlockIndices.increments delimitedBlockLength bodies by
        simp [FiniteBlockIndices.increments, FiniteBlockIndices.markers,
          FiniteUnaryFieldMap.values]]
      rw [increments_block body, induction]

/-- Looking up an aligned key column at the physical block ordinals repeats
each body's key across all of its payload tokens and its delimiter. -/
theorem broadcastKeys_blocks
    [Fintype Alphabet]
    (blockKeys : List Nat) (bodies : List (List Alphabet))
    (aligned : bodies.length = blockKeys.length) :
    broadcastKeys blockKeys (blocks bodies) =
      FiniteBlockIndices.broadcastValues
        delimitedBlockLength bodies blockKeys := by
  unfold broadcastKeys
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt,
    candidateKeys_blocks]
  · rw [FiniteBlockIndices.indices_eq_expected]
    exact FiniteBlockIndices.expected_lookup_eq_broadcastValues
      delimitedBlockLength bodies blockKeys 0 aligned
        (fun body _ => by simp [delimitedBlockLength])
  · intro query member
    have queryLt := FiniteBlockIndices.mem_indices_lt_length
      delimitedBlockLength bodies query
      (by simpa [candidateKeys_blocks] using member)
    simpa only [aligned] using queryLt

end LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookup
