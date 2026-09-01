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

/-- Relational block-level specification of keyed lookup. -/
def expectedBlocks
    (queries blockKeys : List Nat) (bodies : List (List Alphabet)) :
    List (Token Alphabet) :=
  queries.flatMap fun query =>
    (blockKeys.zip bodies).flatMap fun candidate =>
      if query = candidate.1 then block candidate.2 else []

private theorem zip_replicate_length
    (key : Nat) (tokens : List (Token Alphabet)) :
    (List.replicate tokens.length key).zip tokens =
      tokens.map fun token => (key, token) := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp [List.replicate_succ, induction]

private theorem broadcastKeys_blocks_zip
    [Fintype Alphabet]
    (blockKeys : List Nat) (bodies : List (List Alphabet))
    (aligned : bodies.length = blockKeys.length) :
    (broadcastKeys blockKeys (blocks bodies)).zip (blocks bodies) =
      (blockKeys.zip bodies).flatMap fun candidate =>
        (block candidate.2).map fun token => (candidate.1, token) := by
  rw [broadcastKeys_blocks blockKeys bodies aligned]
  unfold FiniteBlockIndices.broadcastValues
  induction bodies generalizing blockKeys with
  | nil =>
      have keysNil : blockKeys = [] :=
        List.eq_nil_of_length_eq_zero aligned.symm
      subst blockKeys
      rfl
  | cons body bodies induction =>
      cases blockKeys with
      | nil => simp at aligned
      | cons key blockKeys =>
          have tailAligned : bodies.length = blockKeys.length := by
            simpa using aligned
          simp only [List.zipWith_cons_cons, List.flatten_cons,
            List.zip_cons_cons, List.flatMap_cons]
          rw [show blocks (body :: bodies) =
              block body ++ blocks bodies by rfl]
          rw [List.zip_append (by
            simp [delimitedBlockLength, block])]
          rw [show List.replicate (delimitedBlockLength body) key =
              List.replicate (block body).length key by
            simp [delimitedBlockLength, block]]
          rw [zip_replicate_length, induction blockKeys tailAligned]

private theorem flatMap_map_key
    (query key : Nat) (tokens : List (Token Alphabet)) :
    (tokens.map fun token => (key, token)).flatMap (fun candidate =>
        if query = candidate.1 then [candidate.2] else []) =
      if query = key then tokens else [] := by
  induction tokens with
  | nil => simp
  | cons token tokens induction =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [induction]
      by_cases same : query = key <;> simp [same]

private theorem flatMap_candidateTokens
    (query : Nat) (candidates : List (Nat × List Alphabet)) :
    (candidates.flatMap (fun candidate =>
        (block candidate.2).map fun token =>
          (candidate.1, token))).flatMap (fun candidate =>
            if query = candidate.1 then [candidate.2] else []) =
      candidates.flatMap fun candidate =>
        if query = candidate.1 then block candidate.2 else [] := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      simp only [List.flatMap_cons, List.flatMap_append]
      rw [flatMap_map_key, induction]

/-- Keyed token lookup is exactly query-major selection of complete matching
bodies; no token from a selected body or its delimiter is lost. -/
theorem selected_blocks
    [Fintype Alphabet]
    (queries blockKeys : List Nat) (bodies : List (List Alphabet))
    (aligned : bodies.length = blockKeys.length) :
    selected queries blockKeys (blocks bodies) =
      expectedBlocks queries blockKeys bodies := by
  rw [selected_eq_expected]
  unfold expected FiniteAlphabetKeyedValueLookup.expected expectedBlocks
  rw [broadcastKeys_blocks_zip blockKeys bodies aligned]
  apply List.flatMap_congr
  intro query _
  exact flatMap_candidateTokens query (blockKeys.zip bodies)

end LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookup
