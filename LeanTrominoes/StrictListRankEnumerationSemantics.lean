/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.StrictListRankEnumerationData
import LeanTrominoes.StrictListRankLookupSemantics

/-! # Exact sorting semantics of strict-rank enumeration -/

namespace LeanTrominoes.StrictListRanks

variable {Value Coordinate : Type*} [LinearOrder Coordinate]

/-- Optional lookup at every valid natural index reconstructs the list. -/
private theorem range_filterMap_getElem?_eq
    (values : List Value) :
    (List.range values.length).filterMap
        (fun index => values[index]?) = values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      rw [show (head :: tail).length = tail.length + 1 by simp]
      rw [List.range_succ_eq_map]
      simp only [List.filterMap_cons, List.getElem?_cons_zero]
      rw [List.filterMap_map]
      change head ::
        (List.range tail.length).filterMap
          (fun index => tail[index]?) = head :: tail
      rw [induction]

/-- Repeated lower-rank lookup reconstructs the exact stable insertion sort
whenever the resulting coordinate order is strict. -/
theorem valuesByLowerRank_eq_insertionSort
    (coordinate : Value → Coordinate) (values : List Value)
    (ordered :
      (values.insertionSort fun first second =>
        coordinate first ≤ coordinate second).Pairwise fun first second =>
          coordinate first < coordinate second) :
    valuesByLowerRank coordinate values =
      values.insertionSort fun first second =>
        coordinate first ≤ coordinate second := by
  let sorted := values.insertionSort fun first second =>
    coordinate first ≤ coordinate second
  unfold valuesByLowerRank
  rw [show values.length = sorted.length by
    simp [sorted]]
  calc
    (List.range sorted.length).filterMap
        (valueAtLowerRank? coordinate values) =
      (List.range sorted.length).filterMap
        (fun index => sorted[index]?) := by
          apply List.filterMap_congr
          intro index indexMember
          have indexLt : index < sorted.length :=
            List.mem_range.mp indexMember
          let value := sorted[index]
          have lookup : sorted[index]? = some value :=
            List.getElem?_eq_getElem indexLt
          calc
            valueAtLowerRank? coordinate values index = some value :=
              valueAtLowerRank?_eq_sorted_getElem?
                coordinate values ordered index value lookup
            _ = sorted[index]? := lookup.symm
    _ = sorted := range_filterMap_getElem?_eq sorted

end LeanTrominoes.StrictListRanks
