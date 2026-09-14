/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling
import Mathlib.Data.List.Chain

/-! # Linear-size certificates that sorted cell lists have no duplicates -/

namespace LeanTrominoes.CompletionCellOrder

def Before (a b : Cell) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

instance (a b : Cell) : Decidable (Before a b) := by unfold Before; infer_instance

instance : IsTrans Cell Before where
  trans a b c hab hbc := by dsimp [Before] at *; omega

theorem nodup (cells : List Cell) (ordered : cells.IsChain Before) : cells.Nodup := by
  have pairwise := ordered.pairwise
  apply List.Pairwise.imp ?_ pairwise
  intro a b before eq
  cases eq
  dsimp [Before] at before
  omega

theorem toFinset_eq (cells : List Cell) (h : cells.Nodup) :
    cells.toFinset = (⟨(↑cells : Multiset Cell),h⟩ : Finset Cell) := by
  ext c
  simp

end LeanTrominoes.CompletionCellOrder
