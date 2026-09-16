/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrominoCompletionAssembly

/-! # Gluing two disjoint completion regions -/
namespace LeanTrominoes.Tromino

theorem Completable.union {t : Tromino} {a b : Set Cell} {p q : Set (Finset Cell)}
    (ha : t.Completable a p) (hb : t.Completable b q) (separate : Disjoint a b) :
    t.Completable (a ∪ b) (p ∪ q) := by
  have localCompletion (i : Bool) : t.Completable (if i then a else b) (if i then p else q) := by
    cases i
    · exact hb
    · exact ha
  have apart (i j : Bool) (c : Cell) (hi : c ∈ if i then a else b) (hj : c ∈ if j then a else b) : i = j := by
    cases i <;> cases j
    · rfl
    · exact False.elim (Set.disjoint_left.mp separate hj hi)
    · exact False.elim (Set.disjoint_left.mp separate hi hj)
    · rfl
  have result := completable_assemble localCompletion apart
  convert result using 1 <;> ext x <;> simp [Bool.exists_bool,or_comm]

end LeanTrominoes.Tromino
