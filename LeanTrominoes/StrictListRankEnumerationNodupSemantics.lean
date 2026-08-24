/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.StrictListRankEnumerationSemantics

/-! # Rank reconstruction from distinct coordinates -/

namespace LeanTrominoes.StrictListRanks

variable {Value Coordinate : Type*} [LinearOrder Coordinate]

/-- A nondecreasing list with no repeated values is strictly increasing. -/
private theorem pairwise_lt_of_pairwise_le_of_nodup
    (coordinates : List Coordinate)
    (ordered : coordinates.Pairwise (· ≤ ·))
    (nodup : coordinates.Nodup) :
    coordinates.Pairwise (· < ·) := by
  induction coordinates with
  | nil => exact .nil
  | cons head tail induction =>
      rw [List.pairwise_cons] at ordered ⊢
      rw [List.nodup_cons] at nodup
      exact ⟨fun other otherMember =>
        lt_of_le_of_ne (ordered.1 other otherMember) fun equal =>
          nodup.1 (equal ▸ otherMember),
        induction ordered.2 nodup.2⟩

/-- If the presented coordinates are distinct, lower-rank enumeration
reconstructs their insertion sort without any separate strict-order
hypothesis. -/
theorem valuesByLowerRank_eq_insertionSort_of_coordinate_nodup
    (coordinate : Value → Coordinate) (values : List Value)
    (coordinateNodup : (values.map coordinate).Nodup) :
    valuesByLowerRank coordinate values =
      values.insertionSort fun first second =>
        coordinate first ≤ coordinate second := by
  let sorted := values.insertionSort fun first second =>
    coordinate first ≤ coordinate second
  have mappedSort := List.map_insertionSort
    (r := fun first second : Value =>
      coordinate first ≤ coordinate second)
    (s := fun first second : Coordinate => first ≤ second)
    coordinate values (by
      intro first firstMember second secondMember
      rfl)
  have mappedNodup : (sorted.map coordinate).Nodup := by
    rw [mappedSort]
    exact (List.perm_insertionSort (· ≤ ·)
      (values.map coordinate)).nodup_iff.mpr coordinateNodup
  have mappedOrdered : (sorted.map coordinate).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact List.pairwise_insertionSort
      (r := fun first second : Value =>
        coordinate first ≤ coordinate second) values
  apply valuesByLowerRank_eq_insertionSort
  rw [show values.insertionSort (fun first second =>
      coordinate first ≤ coordinate second) = sorted by rfl]
  rw [← List.pairwise_map]
  exact pairwise_lt_of_pairwise_le_of_nodup
    (sorted.map coordinate) mappedOrdered mappedNodup

end LeanTrominoes.StrictListRanks
