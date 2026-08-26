/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedConsecutivePairsSemantics

/-! # Adjacent pairs of key-grouped lists -/

namespace LeanTrominoes

open PeriodicOrthocrossing

private theorem consecutivePairs_append_of_ne_nil
    {Value : Type*} (first second : List Value)
    (firstNonempty : first ≠ []) (secondNonempty : second ≠ []) :
    consecutivePairs (first ++ second) =
      consecutivePairs first ++
        [(first.getLast firstNonempty, second.head secondNonempty)] ++
        consecutivePairs second := by
  induction first with
  | nil => contradiction
  | cons value first induction =>
      cases first with
      | nil =>
          cases second with
          | nil => contradiction
          | cons next second =>
              simp [consecutivePairs]
      | cons next first =>
          rw [List.cons_append]
          simp only [consecutivePairs, List.cons_append]
          congr 1
          simpa using induction (by simp)

private theorem filterMap_sameKey_of_forall_key
    {Key Value Output : Type*} [DecidableEq Key]
    (values : List Value) (key : Key) (keyOf : Value → Key)
    (selected : Value → Value → Bool)
    (output : Value → Value → Output)
    (allKey : ∀ value ∈ values, keyOf value = key) :
    (IndexedConsecutivePairs.pairs values).filterMap (fun pair =>
        if decide (keyOf pair.1 = keyOf pair.2) &&
            selected pair.1 pair.2 then
          some (output pair.1 pair.2)
        else none) =
      (IndexedConsecutivePairs.pairs values).filterMap fun pair =>
        if selected pair.1 pair.2 then
          some (output pair.1 pair.2)
        else none := by
  apply List.filterMap_congr
  intro pair pairMember
  have members := mem_of_mem_consecutivePairs
    ((IndexedConsecutivePairs.pairs_eq_consecutivePairs values) ▸ pairMember)
  rw [allKey pair.1 members.1, allKey pair.2 members.2]
  simp

/-- Adjacent pairs of a concatenation of nonempty, distinctly keyed blocks,
after rejecting cross-key boundaries, are exactly the concatenated adjacent
pairs internal to each block. -/
theorem groupedPairs_filterMap
    {Key Value Output : Type*} [DecidableEq Key]
    (keys : List Key) (block : Key → List Value) (keyOf : Value → Key)
    (selected : Value → Value → Bool)
    (output : Value → Value → Output)
    (keysNodup : keys.Nodup)
    (blockNonempty : ∀ key ∈ keys, block key ≠ [])
    (blockKey : ∀ key ∈ keys, ∀ value ∈ block key,
      keyOf value = key) :
    (IndexedConsecutivePairs.pairs (keys.flatMap block)).filterMap
        (fun pair =>
          if decide (keyOf pair.1 = keyOf pair.2) &&
              selected pair.1 pair.2 then
            some (output pair.1 pair.2)
          else none) =
      keys.flatMap fun key =>
        (IndexedConsecutivePairs.pairs (block key)).filterMap fun pair =>
          if selected pair.1 pair.2 then
            some (output pair.1 pair.2)
          else none := by
  simp_rw [IndexedConsecutivePairs.pairs_eq_consecutivePairs]
  induction keys with
  | nil => rfl
  | cons key keys induction =>
      have keyMember : key ∈ key :: keys := by simp
      have keyBlockNonempty := blockNonempty key keyMember
      have keyBlockKey := blockKey key keyMember
      have tailNodup := keysNodup.tail
      have keyNotTail : key ∉ keys :=
        (List.nodup_cons.mp keysNodup).1
      have tailNonempty : ∀ tailKey ∈ keys, block tailKey ≠ [] :=
        fun tailKey tailMember =>
          blockNonempty tailKey (by simp [tailMember])
      have tailKey : ∀ tailKey ∈ keys, ∀ value ∈ block tailKey,
          keyOf value = tailKey :=
        fun tailKey tailMember => blockKey tailKey (by simp [tailMember])
      rw [List.flatMap_cons]
      cases keys with
      | nil =>
          simp only [List.flatMap_nil, List.append_nil]
          simpa [IndexedConsecutivePairs.pairs_eq_consecutivePairs]
            using filterMap_sameKey_of_forall_key
              (block key) key keyOf selected output keyBlockKey
      | cons next keys =>
          let tail := (next :: keys).flatMap block
          have nextMember : next ∈ next :: keys := by simp
          have tailNonemptyProof : tail ≠ [] := by
            unfold tail
            simp only [List.flatMap_cons]
            rcases List.exists_mem_of_ne_nil
                (block next) (tailNonempty next nextMember) with
              ⟨value, valueMember⟩
            intro empty
            have : value ∈ block next ++ keys.flatMap block :=
              List.mem_append_left _ valueMember
            rw [empty] at this
            simp at this
          rw [consecutivePairs_append_of_ne_nil
            (block key) tail keyBlockNonempty tailNonemptyProof]
          rw [List.filterMap_append, List.filterMap_append]
          have firstEq := filterMap_sameKey_of_forall_key
            (block key) key keyOf selected output keyBlockKey
          simp only [IndexedConsecutivePairs.pairs_eq_consecutivePairs]
            at firstEq
          rw [firstEq]
          have tailHeadMember : tail.head tailNonemptyProof ∈ tail :=
            List.head_mem tailNonemptyProof
          rcases List.mem_flatMap.mp tailHeadMember with
            ⟨tailHeadKey, tailHeadKeyMember, tailHeadBlockMember⟩
          have tailHeadKeyEq : keyOf (tail.head tailNonemptyProof) =
              tailHeadKey :=
            tailKey tailHeadKey tailHeadKeyMember
              (tail.head tailNonemptyProof) tailHeadBlockMember
          have lastMember : (block key).getLast keyBlockNonempty ∈ block key :=
            List.getLast_mem keyBlockNonempty
          have lastKeyEq : keyOf ((block key).getLast keyBlockNonempty) = key :=
            keyBlockKey _ lastMember
          have boundaryDifferent :
              keyOf ((block key).getLast keyBlockNonempty) ≠
                keyOf (tail.head tailNonemptyProof) := by
            rw [lastKeyEq, tailHeadKeyEq]
            exact fun equal => keyNotTail (equal ▸ tailHeadKeyMember)
          simp only [List.filterMap_cons, List.filterMap_nil]
          rw [show decide
              (keyOf ((block key).getLast keyBlockNonempty) =
                keyOf (tail.head tailNonemptyProof)) = false by
            simp [boundaryDifferent]]
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          have tailInduction := induction tailNodup tailNonempty tailKey
          simp only [List.append_nil, List.flatMap_cons]
          rw [tailInduction]
          simp only [List.flatMap_cons]

end LeanTrominoes
