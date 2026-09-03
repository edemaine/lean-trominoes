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

/-- The abstract body list selected by the same query-major keyed lookup. -/
def expectedBodyList
    (queries blockKeys : List Nat) (bodies : List (List Alphabet)) :
    List (List Alphabet) :=
  queries.flatMap fun query =>
    (blockKeys.zip bodies).flatMap fun candidate =>
      if query = candidate.1 then [candidate.2] else []

/-- Recover the body aligned with a candidate key at that key's unique
presentation index. -/
def alignedBody
    (blockKeys : List Nat) (bodies : List (List Alphabet))
    (key : Nat) : List Alphabet :=
  bodies.getD (blockKeys.idxOf key) []

/-- An aligned body column over duplicate-free keys is its keywise recovery
map. -/
theorem bodies_eq_map_alignedBody
    (blockKeys : List Nat) (bodies : List (List Alphabet))
    (aligned : blockKeys.length = bodies.length)
    (keysNodup : blockKeys.Nodup) :
    bodies = blockKeys.map (alignedBody blockKeys bodies) := by
  apply List.ext_getElem (by simpa using aligned.symm)
  intro index bodyIndexLt mappedIndexLt
  simp only [List.getElem_map]
  unfold alignedBody
  rw [keysNodup.idxOf_getElem index
    (by simpa [aligned] using bodyIndexLt)]
  exact (List.getD_eq_getElem bodies [] bodyIndexLt).symm

private theorem select_map_alignedBody
    (query : Nat) (blockKeys : List Nat) (body : Nat → List Alphabet)
    (keysNodup : blockKeys.Nodup) :
    (blockKeys.map fun key => (key, body key)).flatMap (fun candidate =>
        if query = candidate.1 then [candidate.2] else []) =
      (if query ∈ blockKeys then [body query] else []) := by
  induction blockKeys with
  | nil => simp
  | cons key keys induction =>
      have ⟨keyNotMem, keysNodup'⟩ := List.nodup_cons.mp keysNodup
      by_cases same : query = key
      · subst key
        simp only [List.map_cons, List.flatMap_cons,
          List.mem_cons, true_or, if_true]
        rw [induction keysNodup', if_neg keyNotMem]
        rfl
      · simp only [List.map_cons, List.flatMap_cons, if_neg same,
          List.nil_append]
        rw [induction keysNodup']
        simp [same]

private theorem zip_map_alignedBody
    (blockKeys : List Nat) (body : Nat → List Alphabet) :
    blockKeys.zip (blockKeys.map body) =
      blockKeys.map fun key => (key, body key) := by
  induction blockKeys with
  | nil => rfl
  | cons key keys induction => simp [induction]

/-- With aligned duplicate-free candidate keys covering every query, the
abstract keyed lookup is exactly the aligned body map in query order. -/
theorem expectedBodyList_eq_map_alignedBody
    (queries blockKeys : List Nat) (bodies : List (List Alphabet))
    (aligned : blockKeys.length = bodies.length)
    (keysNodup : blockKeys.Nodup)
    (present : ∀ query ∈ queries, query ∈ blockKeys) :
    expectedBodyList queries blockKeys bodies =
      queries.map (alignedBody blockKeys bodies) := by
  unfold expectedBodyList
  let body := alignedBody blockKeys bodies
  change _ = queries.map body
  have bodiesEq : bodies = blockKeys.map body :=
    bodies_eq_map_alignedBody blockKeys bodies aligned keysNodup
  have zipped :
      blockKeys.zip (blockKeys.map body) =
        blockKeys.map fun key => (key, body key) :=
    zip_map_alignedBody blockKeys body
  rw [bodiesEq, zipped]
  calc
    _ = queries.flatMap fun query => [body query] := by
      apply List.flatMap_congr
      intro query queryMember
      rw [select_map_alignedBody query blockKeys body keysNodup,
        if_pos (present query queryMember)]
    _ = queries.map body := by
      rw [← List.map_eq_flatMap]

/-- The relational token specification is exactly serialization of its
query-major matching body list. -/
theorem expectedBlocks_eq_blocks
    (queries blockKeys : List Nat) (bodies : List (List Alphabet)) :
    expectedBlocks queries blockKeys bodies =
      blocks (expectedBodyList queries blockKeys bodies) := by
  unfold expectedBlocks expectedBodyList blocks
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro query queryMember
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro candidate candidateMember
  by_cases same : query = candidate.1 <;> simp [same, block]

private theorem matchingBodies_length_eq_count
    (query : Nat) (candidates : List (Nat × List Alphabet)) :
    (candidates.flatMap fun candidate =>
      if query = candidate.1 then [candidate.2] else []).length =
        (candidates.map Prod.fst).count query := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      rw [List.flatMap_cons, List.length_append, induction,
        List.map_cons]
      by_cases same : query = candidate.1
      · simp [same, Nat.add_comm]
      · have reverse : candidate.1 ≠ query := Ne.symm same
        simp [same, reverse]

/-- With aligned duplicate-free keys covering every query, exactly one
abstract body is selected for each query. -/
theorem expectedBodyList_length
    (queries blockKeys : List Nat) (bodies : List (List Alphabet))
    (aligned : bodies.length = blockKeys.length)
    (keysNodup : blockKeys.Nodup)
    (present : ∀ query ∈ queries, query ∈ blockKeys) :
    (expectedBodyList queries blockKeys bodies).length = queries.length := by
  unfold expectedBodyList
  have candidateKeys :
      ((blockKeys.zip bodies).map Prod.fst) = blockKeys :=
    List.map_fst_zip (by omega)
  induction queries with
  | nil => rfl
  | cons query queries induction =>
      have queryPresent : query ∈ blockKeys :=
        present query (by simp)
      have remainingPresent : ∀ other ∈ queries,
          other ∈ blockKeys := by
        intro other member
        exact present other (by simp [member])
      rw [List.flatMap_cons, List.length_append,
        matchingBodies_length_eq_count, candidateKeys,
        List.count_eq_one_of_mem keysNodup queryPresent,
        induction remainingPresent]
      simp only [List.length_cons]
      omega

private theorem zip_replicate_length
    (key : Nat) (tokens : List (Token Alphabet)) :
    (List.replicate tokens.length key).zip tokens =
      tokens.map fun token => (key, token) := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp [List.replicate_succ, induction]

theorem broadcastKeys_blocks_zip
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
