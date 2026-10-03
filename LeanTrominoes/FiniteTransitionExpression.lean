/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTransitionCNF

/-! # Finite-time Tseitin compilation with prescribed endpoints -/
namespace LeanTrominoes.FiniteCNF
open PeriodicCNF

def Pinned (values : Nat → Bool) (pins : List (Nat × Bool)) : Prop :=
  ∀ pin∈pins, values pin.1=pin.2

def pinClauses (time : Nat) (pins : List (Nat × Bool)) : Formula (Nat × Nat) :=
  pins.map fun pin => [((time,pin.1),pin.2)]

theorem satisfies_pinClauses (time : Nat) (pins : List (Nat × Bool)) (values : Nat × Nat → Bool) :
    Satisfies (pinClauses time pins) values ↔ Pinned (fun atom => values (time,atom)) pins := by
  constructor
  · intro h pin hp
    have truth := h _ (List.mem_map.mpr ⟨pin,hp,rfl⟩)
    simpa only [Clause.Holds,List.mem_singleton,exists_eq_left] using truth
  · intro h clause hc
    obtain ⟨pin,hp,rfl⟩ := List.mem_map.mp hc
    exact ⟨((time,pin.1),pin.2),List.mem_singleton_self _,h pin hp⟩

theorem required_nextAtomsBelow (expression : TransitionExpr) (fresh : Nat)
    (bound : expression.AtomsBelow fresh) :
    ClausesNextAtomsBelow (requireTransitionExpr expression fresh).clauses fresh := by
  intro clause hc literal hl offset
  rcases List.mem_append.mp hc with compiled|forced
  · exact compileTransitionExpr_nextAtomsBelow expression fresh bound clause compiled literal hl offset
  · simp only [constantClauses,List.mem_singleton] at forced
    subst clause
    simp only [List.mem_singleton] at hl
    subst literal
    simp [gateOutput,TransitionWire.literal] at offset

/-- Auxiliary values at the next slice may come from a different expression;
only the preserved source bits are read across a transition. -/
theorem realized_transition_to (expression : TransitionExpr) (fresh : Nat)
    (bound : expression.AtomsBelow fresh) (current next other : Nat → Bool)
    (truth : expression.eval current next=true) (agree : ∀ atom<fresh, other atom=next atom) :
    (requireTransitionExpr expression fresh).Transition
      (realizeTransitionExpr expression fresh current next) other := by
  apply (clausesHoldBetween_congr_next (required_nextAtomsBelow expression fresh bound) agree).mpr
  apply (clausesHoldBetween_append_iff _ _ _ _).mpr
  refine ⟨realizeTransitionExpr_holds expression fresh current next bound,?_⟩
  apply (constantClauses_hold_iff _ true _ _).mpr
  exact (realizeTransitionExpr_root expression fresh current next).trans truth

/-- Give each edge its own auxiliary gate values; source bits are unchanged. -/
theorem realized_transition (expression : TransitionExpr) (fresh : Nat)
    (bound : expression.AtomsBelow fresh) (trace : Nat → Nat → Bool) (time : Nat)
    (truth : expression.eval (trace time) (trace (time+1))=true) :
    (requireTransitionExpr expression fresh).Transition
      (realizeTransitionExpr expression fresh (trace time) (trace (time+1)))
      (realizeTransitionExpr expression fresh (trace (time+1)) (trace (time+2))) :=
  realized_transition_to expression fresh bound _ _ _ truth
    (fun atom small => realizeTransitionExpr_preserves expression fresh _ _ small)

def boundedExpression (expression : TransitionExpr) (fresh steps : Nat)
    (initial final : List (Nat × Bool)) : Formula (Nat × Nat) :=
  (pinClauses 0 initial ++ unroll (requireTransitionExpr expression fresh) steps) ++ pinClauses steps final

/-- Exact bounded-trace semantics, including time zero and the final slice. -/
theorem boundedExpression_correct (expression : TransitionExpr) (fresh steps : Nat)
    (initial final : List (Nat × Bool)) (bound : expression.AtomsBelow fresh)
    (initialBound : ∀ pin∈initial, pin.1<fresh) (finalBound : ∀ pin∈final, pin.1<fresh) :
    Satisfiable (boundedExpression expression fresh steps initial final) ↔
      ∃ trace : Nat → Nat → Bool, Pinned (trace 0) initial ∧
        (∀ time<steps, expression.eval (trace time) (trace (time+1))=true) ∧
        Pinned (trace steps) final := by
  constructor
  · rintro ⟨assignment,h⟩
    have parts := (satisfies_append _ _ assignment).mp h
    have front := (satisfies_append _ _ assignment).mp parts.1
    refine ⟨fun time atom => assignment (time,atom),
      (satisfies_pinClauses _ _ _).mp front.1,?_,(satisfies_pinClauses _ _ _).mp parts.2⟩
    intro time ht
    exact requireTransitionExpr_transition_sound expression fresh
      ((satisfies_unroll _ (requireTransitionExpr_forward expression fresh) steps assignment).mp front.2 time ht)
  · rintro ⟨trace,first,follows,last⟩
    let realized := fun time => realizeTransitionExpr expression fresh (trace time) (trace (time+1))
    let assignment := fun p : Nat × Nat => realized p.1 p.2
    have preserves (time atom : Nat) (small : atom<fresh) : realized time atom=trace time atom :=
      realizeTransitionExpr_preserves expression fresh _ _ small
    refine ⟨assignment,(satisfies_append _ _ _).mpr ⟨(satisfies_append _ _ _).mpr ⟨?_,?_⟩,?_⟩⟩
    · apply (satisfies_pinClauses _ _ _).mpr
      intro pin hp
      exact (preserves 0 pin.1 (initialBound pin hp)).trans (first pin hp)
    · apply (satisfies_unroll _ (requireTransitionExpr_forward expression fresh) steps assignment).mpr
      intro time ht
      exact realized_transition expression fresh bound trace time (follows time ht)
    · apply (satisfies_pinClauses _ _ _).mpr
      intro pin hp
      exact (preserves steps pin.1 (finalBound pin hp)).trans (last pin hp)

/-- The number of generated clauses is linear in time and expression size. -/
theorem boundedExpression_length (expression : TransitionExpr) (fresh steps : Nat)
    (initial final : List (Nat × Bool)) :
    (boundedExpression expression fresh steps initial final).length=
      initial.length+steps*(expression.clauseCount+1)+final.length := by
  simp only [boundedExpression,List.length_append,pinClauses,List.length_map,unroll_length,
    requireTransitionExpr,List.length_append,compileTransitionExpr_clause_length,
    constantClauses,List.length_cons,List.length_nil]

end LeanTrominoes.FiniteCNF
