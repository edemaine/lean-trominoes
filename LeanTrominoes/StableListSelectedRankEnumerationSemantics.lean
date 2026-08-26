/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.StableListRankEnumerationSemantics
import LeanTrominoes.StrictListRankEnumerationNodupSemantics

/-! # Stable rank enumeration after selection -/

namespace LeanTrominoes.StableListRanks

variable {Value Coordinate : Type*} [LinearOrder Coordinate]

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

private theorem map_orderedInsert_of_agree_left
    {Tagged Output : Type*}
    {taggedRelation : Tagged → Tagged → Prop}
    {outputRelation : Output → Output → Prop}
    [DecidableRel taggedRelation] [DecidableRel outputRelation]
    (project : Tagged → Output) (value : Tagged) (values : List Tagged)
    (agree : ∀ other ∈ values,
      taggedRelation value other ↔
        outputRelation (project value) (project other)) :
    (values.orderedInsert taggedRelation value).map project =
      (values.map project).orderedInsert outputRelation (project value) := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      by_cases relation : taggedRelation value head
      · rw [List.orderedInsert_cons_of_le taggedRelation tail relation]
        simp only [List.map_cons]
        rw [List.orderedInsert_cons_of_le outputRelation (tail.map project)
          ((agree head List.mem_cons_self).mp relation)]
      · rw [List.orderedInsert_of_not_le taggedRelation tail relation]
        simp only [List.map_cons]
        rw [List.orderedInsert_of_not_le outputRelation (tail.map project)
          fun projected => relation
            ((agree head List.mem_cons_self).mpr projected)]
        congr 1
        exact induction fun other otherMember =>
          agree other (List.mem_cons_of_mem head otherMember)

private theorem filtered_zipIdx_insertionSort_map_fst
    (coordinate : Value → Coordinate) (selected : Value → Bool)
    (values : List Value) (start : Nat) :
    (((values.zipIdx start).filter fun entry => selected entry.1).insertionSort
        fun first second =>
          indexedCoordinate coordinate first ≤
            indexedCoordinate coordinate second).map Prod.fst =
      (values.filter selected).insertionSort fun first second =>
        coordinate first ≤ coordinate second := by
  induction values generalizing start with
  | nil => rfl
  | cons head tail induction =>
      by_cases active : selected head
      · simp only [List.zipIdx_cons, List.filter_cons, active, if_true,
          List.insertionSort_cons]
        rw [map_orderedInsert_of_agree_left
          (taggedRelation := fun first second : Value × Nat =>
            indexedCoordinate coordinate first ≤
              indexedCoordinate coordinate second)
          (outputRelation := fun first second : Value =>
            coordinate first ≤ coordinate second)]
        · rw [induction (start + 1)]
        · intro other otherMember
          have filteredMember :
              other ∈ (tail.zipIdx (start + 1)).filter fun entry =>
                selected entry.1 := by
            simpa only [List.mem_insertionSort] using otherMember
          have tailMember : other ∈ tail.zipIdx (start + 1) :=
            (List.mem_filter.mp filteredMember).1
          have indexLe : start ≤ other.2 :=
            (Nat.le_succ start).trans
              (start_le_snd_of_mem_zipIdx tail (start + 1) other tailMember)
          rw [show indexedCoordinate coordinate (head, start) =
              toLex (coordinate head, start) by rfl]
          rw [show indexedCoordinate coordinate other =
              toLex (coordinate other.1, other.2) by rfl]
          rw [Prod.Lex.toLex_le_toLex]
          constructor
          · rintro (strict | ⟨equal, _⟩)
            · exact strict.le
            · exact equal.le
          · intro coordinateLe
            rcases coordinateLe.eq_or_lt with equal | strict
            · exact Or.inr ⟨equal, indexLe⟩
            · exact Or.inl strict
      · have inactive : selected head = false :=
          Bool.eq_false_of_not_eq_true active
        simp only [List.zipIdx_cons, List.filter_cons, inactive]
        exact induction (start + 1)

/-- Selecting values while retaining their original indices and then
strict-rank sorting projects to the stable lower-rank enumeration of the
selected values. -/
theorem selectedIndexedValuesByLowerRank_map_fst
    (coordinate : Value → Coordinate) (selected : Value → Bool)
    (values : List Value) :
    (StrictListRanks.valuesByLowerRank
        (indexedCoordinate coordinate)
        (values.zipIdx.filter fun entry => selected entry.1)).map Prod.fst =
      valuesByStableLowerRank coordinate (values.filter selected) := by
  have coordinateNodup :
      (((values.zipIdx.filter fun entry => selected entry.1).map
        (indexedCoordinate coordinate))).Nodup :=
    (indexedCoordinate_zipIdx_nodup coordinate values).sublist
      (List.filter_sublist.map (indexedCoordinate coordinate))
  rw [StrictListRanks.valuesByLowerRank_eq_insertionSort_of_coordinate_nodup
    (indexedCoordinate coordinate)
    (values.zipIdx.filter fun entry => selected entry.1) coordinateNodup]
  rw [filtered_zipIdx_insertionSort_map_fst coordinate selected values 0]
  exact (valuesByStableLowerRank_eq_insertionSort
    coordinate (values.filter selected)).symm

end LeanTrominoes.StableListRanks
