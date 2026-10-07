/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFSignedDecoder

/-! # A single finite window suffices for every clause of a fixed local decoder -/
namespace LeanTrominoes.PeriodicCNF.SignedDecoder
variable {V W : Type} [DecidableEq W]

theorem boxCellList_mono {small large : Nat} (bound : small ≤ large) :
    ∀ c ∈ TrominoAssignment.boxCellList small, c ∈ TrominoAssignment.boxCellList large := by
  intro c member
  rw [TrominoAssignment.mem_boxCellList_iff] at member ⊢
  unfold LeanWang.InBox at member ⊢
  omega

private theorem clauses_uniform_window (target : PeriodicCNF W) (read : Read V W)
    (clauses : List (PeriodicClause V))
    (forced : ∀ clause ∈ clauses, ∃ r, FiniteConsequences.FiniteEntails target (groundClause read clause) r) :
    ∃ radius, ∀ a : W → Cell → Bool, ∀ translate : Cell,
      (∀ c ∈ TrominoAssignment.boxCellList radius,
        ∀ clause ∈ target.clauses, clause.Holds a (Cell.add translate c)) →
      ∀ clause ∈ clauses, clause.Holds (decode read a) translate := by
  induction clauses with
  | nil => exact ⟨0,fun _ _ _ _ member => False.elim (List.not_mem_nil member)⟩
  | cons clause rest ih =>
    obtain ⟨first,firstForced⟩ := forced clause (List.mem_cons_self)
    obtain ⟨tail,tailForced⟩ := ih (fun c member => forced c (List.mem_cons_of_mem _ member))
    refine ⟨max first tail,?_⟩
    intro a translate patch c member
    rcases List.mem_cons.mp member with equal | member
    · subst c
      exact local_clause firstForced a translate
        (fun cell hc => patch cell (boxCellList_mono (Nat.le_max_left _ _) cell hc))
    · exact tailForced a translate
        (fun cell hc => patch cell (boxCellList_mono (Nat.le_max_right _ _) cell hc)) c member

theorem uniform_local_window {source : PeriodicCNF V} {target : PeriodicCNF W} {read : Read V W}
    (sound : ∀ a, target.Satisfies a → source.Satisfies (decode read a)) :
    ∃ radius, ∀ a : W → Cell → Bool, ∀ translate : Cell,
      (∀ c ∈ TrominoAssignment.boxCellList radius,
        ∀ clause ∈ target.clauses, clause.Holds a (Cell.add translate c)) →
      ∀ clause ∈ source.clauses, clause.Holds (decode read a) translate :=
  clauses_uniform_window target read source.clauses (finite_radius sound)

end LeanTrominoes.PeriodicCNF.SignedDecoder
