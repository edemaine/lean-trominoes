/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.Finset.Card

/-! # Cardinality of lists with the same membership predicate -/

namespace List

/-- Two finite lists with the same elements have deduplications of the same
length, independently of their order and multiplicities. -/
theorem dedup_length_eq_of_mem_iff
    {α : Type*} [DecidableEq α]
    (first second : List α)
    (sameMembers : ∀ atom, atom ∈ first ↔ atom ∈ second) :
    first.dedup.length = second.dedup.length := by
  rw [← toFinset_card_of_nodup (nodup_dedup first),
    ← toFinset_card_of_nodup (nodup_dedup second)]
  congr 1
  ext atom
  simp only [mem_toFinset, mem_dedup]
  exact sameMembers atom

end List
