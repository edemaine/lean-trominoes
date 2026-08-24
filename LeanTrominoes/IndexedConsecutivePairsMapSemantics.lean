/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedConsecutivePairsSemantics

/-! # Mapping indexed adjacent-pair enumerations -/

namespace LeanTrominoes.IndexedConsecutivePairs

/-- Mapping values before indexed adjacency is the same as mapping both
endpoints of every indexed pair. -/
theorem pairs_map {Value Output : Type*}
    (values : List Value) (mapping : Value → Output) :
    pairs (values.map mapping) =
      (pairs values).map fun pair =>
        (mapping pair.1, mapping pair.2) := by
  rw [pairs_eq_consecutivePairs, pairs_eq_consecutivePairs]
  induction values using List.twoStepInduction with
  | nil => rfl
  | singleton value => rfl
  | cons_cons first second rest _ tailInduction =>
      simp only [List.map_cons,
        PeriodicOrthocrossing.consecutivePairs]
      congr 1
      exact tailInduction second

end LeanTrominoes.IndexedConsecutivePairs
