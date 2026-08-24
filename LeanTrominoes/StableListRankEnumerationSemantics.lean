/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Sigma
import LeanTrominoes.StableListRankEnumerationData
import LeanTrominoes.StrictListRankEnumerationNodupSemantics

/-! # Exact stable-sort semantics of indexed lower ranks -/

namespace LeanTrominoes.StableListRanks

variable {Value Coordinate : Type*}

/-- Every index in `zipIdx start` is at least `start`. -/
private theorem start_le_snd_of_mem_zipIdx
    (values : List Value) (start : Nat) (entry : Value × Nat)
    (member : entry ∈ values.zipIdx start) :
    start ≤ entry.2 := by
  induction values generalizing start with
  | nil => simp at member
  | cons head tail induction =>
      rw [List.zipIdx_cons] at member
      rcases List.mem_cons.mp member with equal | tailMember
      · subst entry
        exact Nat.le_refl start
      · exact (Nat.le_succ start).trans
          (induction (start + 1) tailMember)

/-- Ordered insertion agrees for two relations whenever they make the same
decision between the inserted value and every presented value. -/
private theorem orderedInsert_eq_of_agree_left
    {Element : Type*} {firstRelation secondRelation : Element → Element → Prop}
    [DecidableRel firstRelation] [DecidableRel secondRelation]
    (value : Element) (values : List Element)
    (agree : ∀ other ∈ values,
      firstRelation value other ↔ secondRelation value other) :
    values.orderedInsert firstRelation value =
      values.orderedInsert secondRelation value := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      by_cases relation : firstRelation value head
      · rw [List.orderedInsert_cons_of_le firstRelation tail relation]
        rw [List.orderedInsert_cons_of_le secondRelation tail
          ((agree head List.mem_cons_self).mp relation)]
      · rw [List.orderedInsert_of_not_le firstRelation tail relation]
        rw [List.orderedInsert_of_not_le secondRelation tail fun second =>
          relation ((agree head List.mem_cons_self).mpr second)]
        congr 1
        exact induction fun other otherMember =>
          agree other (List.mem_cons_of_mem head otherMember)

/-- Indexed coordinate pairs have no duplicates, independently of duplicate
values or duplicate coordinates in the underlying presentation. -/
theorem indexedCoordinate_zipIdx_nodup
    (coordinate : Value → Coordinate) (values : List Value) :
    ((values.zipIdx).map (indexedCoordinate coordinate)).Nodup := by
  have indexNodup := List.nodup_zipIdx_map_snd values
  have entriesNodup : values.zipIdx.Nodup :=
    List.Nodup.of_map Prod.snd indexNodup
  apply entriesNodup.map_on
  intro first firstMember second secondMember equal
  apply List.inj_on_of_nodup_map indexNodup firstMember secondMember
  exact congrArg (fun entry : Coordinate ×ₗ Nat => (ofLex entry).2) equal

variable [LinearOrder Coordinate]

/-- Sorting indexed values lexicographically by `(coordinate, index)` is
the same tagged list as stable insertion sorting by coordinate alone. -/
private theorem zipIdx_insertionSort_indexedCoordinate_eq
    (coordinate : Value → Coordinate) (values : List Value) (start : Nat) :
    (values.zipIdx start).insertionSort fun first second =>
        indexedCoordinate coordinate first ≤
          indexedCoordinate coordinate second =
      (values.zipIdx start).insertionSort fun first second =>
        coordinate first.1 ≤ coordinate second.1 := by
  induction values generalizing start with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.zipIdx_cons, List.insertionSort_cons]
      rw [induction (start + 1)]
      apply orderedInsert_eq_of_agree_left
      intro other otherMember
      have originalMember : other ∈ tail.zipIdx (start + 1) := by
        simpa only [List.mem_insertionSort] using otherMember
      have indexLt : start < other.2 :=
        (Nat.lt_succ_self start).trans_le
          (start_le_snd_of_mem_zipIdx
            tail (start + 1) other originalMember)
      rw [show indexedCoordinate coordinate (head, start) =
          toLex (coordinate head, start) by rfl]
      rw [show indexedCoordinate coordinate other =
          toLex (coordinate other.1, other.2) by rfl]
      rw [Prod.Lex.toLex_le_toLex]
      constructor
      · rintro (strict | ⟨equal, indexLe⟩)
        · exact strict.le
        · exact equal.le
      · intro coordinateLe
        rcases coordinateLe.eq_or_lt with equal | strict
        · exact Or.inr ⟨equal, indexLt.le⟩
        · exact Or.inl strict

/-- Stable lower-rank enumeration is exactly Lean's stable insertion sort,
with no distinct-coordinate or geometric-order hypothesis. -/
theorem valuesByStableLowerRank_eq_insertionSort
    (coordinate : Value → Coordinate) (values : List Value) :
    valuesByStableLowerRank coordinate values =
      values.insertionSort fun first second =>
        coordinate first ≤ coordinate second := by
  unfold valuesByStableLowerRank
  rw [StrictListRanks.valuesByLowerRank_eq_insertionSort_of_coordinate_nodup
    (indexedCoordinate coordinate) values.zipIdx
    (indexedCoordinate_zipIdx_nodup coordinate values)]
  rw [zipIdx_insertionSort_indexedCoordinate_eq coordinate values 0]
  have mappedSort := List.map_insertionSort
    (r := fun first second : Value × Nat =>
      coordinate first.1 ≤ coordinate second.1)
    (s := fun first second : Value =>
      coordinate first ≤ coordinate second)
    Prod.fst values.zipIdx (by
      intro first firstMember second secondMember
      rfl)
  rw [mappedSort]
  exact congrArg
    (fun presented : List Value =>
      presented.insertionSort fun first second =>
        coordinate first ≤ coordinate second)
    (List.zipIdx_map_fst 0 values)

end LeanTrominoes.StableListRanks
