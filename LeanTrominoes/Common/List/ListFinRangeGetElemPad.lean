/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.FinRange

/-! # Enumerating optional list lookups with fixed padding -/

namespace List

/-- Optional lookups over a natural range enumerate the source values
followed by exactly enough inactive padding. -/
theorem map_range_getElem?_eq_pad
    (values : List α) (count : Nat) (bound : values.length ≤ count) :
    (List.range count).map (fun index => values[index]?) =
      values.map some ++ List.replicate (count - values.length) none := by
  induction count generalizing values with
  | zero =>
      have valuesLength : values.length = 0 := by omega
      have valuesEq : values = [] :=
        List.eq_nil_of_length_eq_zero valuesLength
      subst values
      rfl
  | succ count induction =>
      cases values with
      | nil => simp
      | cons value values =>
          have tailBound : values.length ≤ count := by
            simp only [List.length_cons] at bound
            omega
          rw [List.range_succ_eq_map]
          simp only [List.map_cons, List.map_map,
            List.getElem?_cons_zero, List.length_cons]
          rw [show count + 1 - (values.length + 1) =
              count - values.length by omega]
          have lookupComp :
              ((fun index => (value :: values)[index]?) ∘ Nat.succ) =
                (fun index => values[index]?) := by
            funext index
            rfl
          rw [lookupComp]
          rw [induction values tailBound]
          rfl

/-- The values of `Fin count` occur in the same order as the natural range. -/
theorem map_finRange_val (count : Nat) :
    (List.finRange count).map Fin.val = List.range count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.finRange_succ_last, List.map_append, List.map_map,
        List.range_succ]
      rw [show (Fin.val ∘ Fin.castSucc) = Fin.val by
        funext index
        rfl]
      rw [induction]
      rfl

/-- Optional lookups at every fixed `Fin` index enumerate the source values
followed by exactly enough inactive padding. -/
theorem map_finRange_getElem?_eq_pad
    (values : List α) (count : Nat) (bound : values.length ≤ count) :
    (List.finRange count).map (fun index => values[index.val]?) =
      values.map some ++ List.replicate (count - values.length) none := by
  calc
    (List.finRange count).map (fun index => values[index.val]?) =
      ((List.finRange count).map Fin.val).map
        (fun index => values[index]?) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro index _indexMember
          rfl
    _ = (List.range count).map (fun index => values[index]?) := by
      rw [List.map_finRange_val]
    _ = _ := List.map_range_getElem?_eq_pad values count bound

end List
