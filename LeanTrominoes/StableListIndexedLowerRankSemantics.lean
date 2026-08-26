/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.StableListRankEnumerationSemantics
import LeanTrominoes.StrictListRankEnumerationNodupSemantics

/-! # Lower ranks of selected, presentation-indexed values -/

namespace LeanTrominoes.StableListRanks

variable {Value Coordinate : Type*} [LinearOrder Coordinate]

/-- Strict lower rank after retaining a selected fiber while preserving the
original presentation indices. -/
def selectedIndexedLowerRank (coordinate : Value → Coordinate)
    (selected : Value → Bool) (values : List Value)
    (entry : Value × Nat) : Nat :=
  StrictListRanks.lowerRank (indexedCoordinate coordinate)
    (values.zipIdx.filter fun other => selected other.1) entry

private theorem lowerRank_filter_zipIdx_before
    (coordinate : Value → Coordinate) (selected : Value → Bool)
    (values : List Value) (start target : Nat) (value : Value)
    (before : target ≤ start) :
    StrictListRanks.lowerRank (indexedCoordinate coordinate)
        ((values.zipIdx start).filter fun other => selected other.1)
        (value, target) =
      (values.filter fun other =>
        selected other && decide (coordinate other < coordinate value)).length := by
  induction values generalizing start with
  | nil => rfl
  | cons head tail induction =>
      have headLt :
          indexedCoordinate coordinate (head, start) <
              indexedCoordinate coordinate (value, target) ↔
            coordinate head < coordinate value := by
        rw [show indexedCoordinate coordinate (head, start) =
            toLex (coordinate head, start) by rfl]
        rw [show indexedCoordinate coordinate (value, target) =
            toLex (coordinate value, target) by rfl]
        rw [Prod.Lex.toLex_lt_toLex]
        constructor
        · rintro (strict | ⟨_equal, indexLt⟩)
          · exact strict
          · omega
        · exact Or.inl
      have tailRank := induction (start + 1)
        (before.trans (by omega))
      unfold StrictListRanks.lowerRank at tailRank ⊢
      simp only [List.zipIdx_cons, List.filter_cons,
        List.filter_filter] at tailRank ⊢
      by_cases active : selected head <;>
        by_cases strict : coordinate head < coordinate value <;> {
          simp [active, strict, headLt]
          exact tailRank }

private theorem selectedIndexedLowerRankFrom_eq
    (coordinate : Value → Coordinate) (selected : Value → Bool)
    (values : List Value) (start index : Nat) (value : Value)
    (lookup : values[index]? = some value) :
    StrictListRanks.lowerRank (indexedCoordinate coordinate)
        ((values.zipIdx start).filter fun other => selected other.1)
        (value, start + index) =
      (values.filter fun other =>
        selected other && decide (coordinate other < coordinate value)).length +
      ((values.take index).filter fun other =>
        selected other && decide (coordinate other = coordinate value)).length := by
  induction values generalizing start index with
  | nil => simp at lookup
  | cons head tail induction =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
          subst value
          have tailRank := lowerRank_filter_zipIdx_before
            coordinate selected tail (start + 1) start head (by omega)
          unfold StrictListRanks.lowerRank at tailRank ⊢
          simp only [Nat.add_zero, List.zipIdx_cons, List.filter_cons,
            List.filter_filter, List.take_zero, List.filter_nil,
            List.length_nil, Nat.add_zero] at tailRank ⊢
          by_cases active : selected head <;> {
            simp [active]
            exact tailRank }
      | succ index =>
          simp only [List.getElem?_cons_succ] at lookup
          have targetEq : start + Nat.succ index =
              (start + 1) + index := by omega
          rw [targetEq]
          have tailRank := induction (start + 1) index lookup
          have headLt :
              indexedCoordinate coordinate (head, start) <
                  indexedCoordinate coordinate
                    (value, (start + 1) + index) ↔
                coordinate head < coordinate value ∨
                  coordinate head = coordinate value := by
            rw [show indexedCoordinate coordinate (head, start) =
                toLex (coordinate head, start) by rfl]
            rw [show indexedCoordinate coordinate
                  (value, (start + 1) + index) =
                toLex (coordinate value, (start + 1) + index) by rfl]
            rw [Prod.Lex.toLex_lt_toLex]
            simp only
            constructor
            · rintro (strict | ⟨equal, _indexLt⟩)
              · exact Or.inl strict
              · exact Or.inr equal
            · rintro (strict | equal)
              · exact Or.inl strict
              · exact Or.inr ⟨equal, by omega⟩
          unfold StrictListRanks.lowerRank at tailRank ⊢
          simp only [List.zipIdx_cons, List.filter_cons,
            List.filter_filter, List.take_succ_cons] at tailRank ⊢
          by_cases active : selected head
          · rcases lt_trichotomy (coordinate head) (coordinate value) with
              strict | equal | greater
            · simp [active, strict, ne_of_lt strict, headLt]
              rw [tailRank]
              omega
            · simp [active, equal, headLt]
              rw [tailRank]
              omega
            · have notStrict : ¬coordinate head < coordinate value :=
                not_lt_of_ge greater.le
              have notEqual : coordinate head ≠ coordinate value :=
                ne_of_gt greater
              simp [active, notStrict, notEqual, headLt]
              exact tailRank
          · simp [active]
            exact tailRank

/-- The lower rank of a value tagged by its presentation index is the number
of selected strict-coordinate predecessors plus selected equal-coordinate
predecessors in its presentation prefix. -/
theorem selectedIndexedLowerRank_eq
    (coordinate : Value → Coordinate) (selected : Value → Bool)
    (values : List Value) (index : Nat) (value : Value)
    (lookup : values[index]? = some value) :
    selectedIndexedLowerRank coordinate selected values (value, index) =
      (values.filter fun other =>
        selected other && decide (coordinate other < coordinate value)).length +
      ((values.take index).filter fun other =>
        selected other && decide (coordinate other = coordinate value)).length := by
  unfold selectedIndexedLowerRank
  simpa using selectedIndexedLowerRankFrom_eq
    coordinate selected values 0 index value lookup

/-- A selected indexed value's stable lower rank is its exact index in the
strict-rank enumeration of the selected, globally indexed presentation. -/
theorem selectedIndexedLowerRank_eq_idxOf_rankEnumeration
    [DecidableEq Value]
    (coordinate : Value → Coordinate) (selected : Value → Bool)
    (values : List Value) (entry : Value × Nat)
    (member : entry ∈ values.zipIdx)
    (selectedEntry : selected entry.1 = true) :
    selectedIndexedLowerRank coordinate selected values entry =
      @List.idxOf (Value × Nat) instBEqOfDecidableEq entry
        (StrictListRanks.valuesByLowerRank
          (indexedCoordinate coordinate)
          (values.zipIdx.filter fun other => selected other.1)) := by
  let tagged := values.zipIdx.filter fun other => selected other.1
  have coordinateNodup :
      (tagged.map (indexedCoordinate coordinate)).Nodup := by
    exact (indexedCoordinate_zipIdx_nodup coordinate values).sublist
      (List.filter_sublist.map (indexedCoordinate coordinate))
  have taggedMember : entry ∈ tagged := by
    simp [tagged, member, selectedEntry]
  unfold selectedIndexedLowerRank
  exact
    StrictListRanks.lowerRank_eq_idxOf_valuesByLowerRank_of_coordinate_nodup
      (indexedCoordinate coordinate) tagged coordinateNodup entry taggedMember

end LeanTrominoes.StableListRanks
