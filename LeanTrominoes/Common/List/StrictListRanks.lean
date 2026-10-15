/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Sort

/-! # Rank reconstruction for strictly ordered finite lists -/

namespace LeanTrominoes.StrictListRanks

variable {Value Coordinate : Type*}
  [LinearOrder Coordinate]

/-- The zero-based rank of `value`, computed without sorting: count the
presented values having a strictly smaller coordinate. -/
def lowerRank (coordinate : Value → Coordinate)
    (values : List Value) (value : Value) : Nat :=
  (values.filter fun other => coordinate other < coordinate value).length

/-- In a strictly coordinate-ordered list, pairwise lower-counting recovers
the exact list index.  This is the basic semantic bridge that lets a machine
enumerate geometric nodes by rank instead of implementing an encoded sort. -/
theorem lowerRank_eq_index_of_getElem?
    (coordinate : Value → Coordinate) (values : List Value)
    (ordered : values.Pairwise fun first second =>
      coordinate first < coordinate second)
    (index : Nat) (value : Value)
    (lookup : values[index]? = some value) :
    lowerRank coordinate values value = index := by
  induction values generalizing index with
  | nil =>
      simp at lookup
  | cons head tail induction =>
      rw [List.pairwise_cons] at ordered
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
          subst value
          have noLower :
              tail.filter (fun other =>
                coordinate other < coordinate head) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro other otherMember
            simpa using not_lt_of_ge
              (ordered.1 other otherMember).le
          simp [lowerRank, noLower]
      | succ index =>
          simp only [List.getElem?_cons_succ] at lookup
          have valueMember : value ∈ tail :=
            List.mem_of_getElem? lookup
          have headLower : coordinate head < coordinate value :=
            ordered.1 value valueMember
          change
            ((head :: tail).filter (fun other =>
              coordinate other < coordinate value)).length =
              Nat.succ index
          rw [show
            (head :: tail).filter (fun other =>
                coordinate other < coordinate value) =
              head :: tail.filter (fun other =>
                coordinate other < coordinate value) by
            simp [headLower]]
          simp only [List.length_cons, Nat.succ.injEq]
          exact induction ordered.2 index lookup

/-- Counting lower coordinates in the original presentation gives the index
of the same value in its strictly ordered insertion sort.  Thus rank-major
enumeration needs comparisons and counting, but no materialized sort. -/
theorem lowerRank_eq_sortedIndex_of_getElem?
    (coordinate : Value → Coordinate) (values : List Value)
    (ordered :
      (values.insertionSort fun first second =>
        coordinate first ≤ coordinate second).Pairwise fun first second =>
          coordinate first < coordinate second)
    (index : Nat) (value : Value)
    (lookup :
      (values.insertionSort fun first second =>
        coordinate first ≤ coordinate second)[index]? = some value) :
    lowerRank coordinate values value = index := by
  let sorted := values.insertionSort fun first second =>
    coordinate first ≤ coordinate second
  have rankPermutation : List.Perm
      (sorted.filter fun other =>
        coordinate other < coordinate value)
      (values.filter fun other =>
        coordinate other < coordinate value) :=
    (List.perm_insertionSort
      (fun first second => coordinate first ≤ coordinate second)
      values).filter _
  calc
    lowerRank coordinate values value =
        lowerRank coordinate sorted value := by
      exact rankPermutation.length_eq.symm
    _ = index :=
      lowerRank_eq_index_of_getElem?
        coordinate sorted ordered index value lookup

end LeanTrominoes.StrictListRanks
