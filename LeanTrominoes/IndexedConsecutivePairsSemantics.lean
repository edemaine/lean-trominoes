/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedConsecutivePairsData

/-! # Correctness of indexed adjacent-pair enumeration -/

namespace LeanTrominoes.IndexedConsecutivePairs

/-- Natural-range lookup enumerates adjacent pairs in exactly the recursive
order of `PeriodicOrthocrossing.consecutivePairs`. -/
theorem pairs_eq_consecutivePairs {Value : Type*} (values : List Value) :
    pairs values = PeriodicOrthocrossing.consecutivePairs values := by
  induction values using List.twoStepInduction with
  | nil => rfl
  | singleton value => rfl
  | cons_cons first second rest _ tailInduction =>
      unfold pairs
      rw [show (first :: second :: rest).length =
        (second :: rest).length + 1 by simp]
      rw [List.range_succ_eq_map]
      simp only [List.filterMap_cons, pairAt?,
        List.getElem?_cons_zero]
      change
        (first, second) ::
          ((List.range (second :: rest).length).map Nat.succ).filterMap
            (pairAt? (first :: second :: rest)) =
        (first, second) ::
          PeriodicOrthocrossing.consecutivePairs (second :: rest)
      congr 1
      rw [List.filterMap_map]
      change
        (List.range (second :: rest).length).filterMap
            (pairAt? (second :: rest)) =
          PeriodicOrthocrossing.consecutivePairs (second :: rest)
      exact tailInduction second

end LeanTrominoes.IndexedConsecutivePairs
