/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTraceCNF
import Mathlib.Data.Nat.Pairing

/-! # Variable ranges in finite computation tableaux -/
namespace LeanTrominoes.FiniteCNF
open PeriodicCNF

theorem required_atomsBelow (expression : TransitionExpr) (fresh : Nat)
    (source : expression.AtomsBelow fresh) :
    ClausesAtomsBelow (requireTransitionExpr expression fresh).clauses (fresh+expression.gateCount) := by
  intro clause member literal hl
  rcases List.mem_append.mp member with compiled|forced
  · simpa only [compileTransitionExpr_nextFresh] using
      compileTransitionExpr_atomsBelow expression fresh source clause compiled literal hl
  · exact constantClauses_atomsBelow
      (by simpa only [compileTransitionExpr_nextFresh] using compileTransitionExpr_root_lt_nextFresh expression fresh)
      true clause forced literal hl

theorem traceFormula_variable_bounds (expressions : Nat → TransitionExpr)
    (fresh steps gateBound : Nat)
    (source : ∀ time < steps, (expressions time).AtomsBelow fresh)
    (gates : ∀ time < steps, (expressions time).gateCount ≤ gateBound)
    (clause : Clause (Nat × Nat)) (member : clause∈traceFormula expressions fresh steps)
    (literal : Literal (Nat × Nat)) (hl : literal∈clause) :
    literal.1.1 ≤ steps ∧ literal.1.2 < fresh+gateBound := by
  obtain ⟨time,ht,member⟩ := List.mem_flatMap.mp member
  have early : time < steps := List.mem_range.mp ht
  obtain ⟨original,hm,rfl⟩ := List.mem_map.mp member
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hl
  have atom := required_atomsBelow (expressions time) fresh (source time early) original hm old ho
  have gate := gates time early
  unfold timeLiteral
  split_ifs <;> dsimp <;> omega

theorem satisfiable_pair_rename (formula : Formula (Nat × Nat)) :
    Satisfiable (rename Nat.pairEquiv formula) ↔ Satisfiable formula := by
  constructor
  · rintro ⟨assignment,h⟩
    exact ⟨assignment ∘ Nat.pairEquiv,(satisfies_rename _ _ _).mp h⟩
  · rintro ⟨assignment,h⟩
    refine ⟨assignment ∘ Nat.unpair,(satisfies_rename _ _ _).mpr ?_⟩
    have composed : (assignment ∘ Nat.unpair) ∘ Nat.pairEquiv=assignment := by
      funext p
      rcases p with ⟨a,b⟩
      simp [Function.comp_def,Nat.pairEquiv]
    simpa only [composed] using h

end LeanTrominoes.FiniteCNF
