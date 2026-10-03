/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTransitionExpression

/-! # Finite CNF for time-dependent bounded computation constraints

Initial and final constraints can be attached to their own time slices.
All auxiliary variables remain private to one transition, while the source
variables are shared with the adjacent transition.
-/
namespace LeanTrominoes.FiniteCNF
open PeriodicCNF

def traceFormula (expressions : Nat → TransitionExpr) (fresh steps : Nat) : Formula (Nat × Nat) :=
  (List.range steps).flatMap fun time => atTime (requireTransitionExpr (expressions time) fresh) time

theorem satisfies_traceFormula (expressions : Nat → TransitionExpr) (fresh steps : Nat)
    (assignment : Nat × Nat → Bool) :
    Satisfies (traceFormula expressions fresh steps) assignment ↔
      ∀ time<steps, (requireTransitionExpr (expressions time) fresh).Transition
        (fun atom => assignment (time,atom)) (fun atom => assignment (time+1,atom)) := by
  change (∀ clause∈(List.range steps).flatMap _, Clause.Holds assignment clause) ↔ _
  simp only [List.mem_flatMap,List.mem_range,forall_exists_index,and_imp]
  constructor
  · intro h time ht
    exact (satisfies_atTime _ (requireTransitionExpr_forward _ _) time assignment).mp
      (fun clause hc => h clause time ht hc)
  · intro h clause time ht hc
    exact (satisfies_atTime _ (requireTransitionExpr_forward _ _) time assignment).mpr (h time ht) clause hc

theorem traceFormula_correct (expressions : Nat → TransitionExpr) (fresh steps : Nat)
    (bounds : ∀ time<steps, (expressions time).AtomsBelow fresh) :
    Satisfiable (traceFormula expressions fresh steps) ↔
      ∃ trace : Nat → Nat → Bool, ∀ time<steps,
        (expressions time).eval (trace time) (trace (time+1))=true := by
  constructor
  · rintro ⟨assignment,h⟩
    refine ⟨fun time atom => assignment (time,atom),?_⟩
    intro time ht
    exact requireTransitionExpr_transition_sound _ _
      ((satisfies_traceFormula expressions fresh steps assignment).mp h time ht)
  · rintro ⟨trace,h⟩
    let realized := fun time => realizeTransitionExpr (expressions time) fresh (trace time) (trace (time+1))
    refine ⟨fun p => realized p.1 p.2,(satisfies_traceFormula expressions fresh steps _).mpr ?_⟩
    intro time ht
    exact realized_transition_to _ _ (bounds time ht) _ _ _ (h time ht)
      (fun atom small => realizeTransitionExpr_preserves (expressions (time+1)) fresh _ _ small)

theorem clauseCount_le (expression : TransitionExpr) : expression.clauseCount≤3*expression.gateCount := by
  induction expression with
  | constant value => simp [TransitionExpr.clauseCount,TransitionExpr.gateCount]
  | wire input => simp [TransitionExpr.clauseCount,TransitionExpr.gateCount]
  | not expression ih => simp only [TransitionExpr.clauseCount,TransitionExpr.gateCount]; omega
  | and first second ih1 ih2 => simp only [TransitionExpr.clauseCount,TransitionExpr.gateCount]; omega
  | or first second ih1 ih2 => simp only [TransitionExpr.clauseCount,TransitionExpr.gateCount]; omega

/-- An explicit size bound, including a separate root constraint at each time. -/
theorem traceFormula_length_le (expressions : Nat → TransitionExpr) (fresh steps gateBound : Nat)
    (bounds : ∀ time<steps, (expressions time).gateCount≤gateBound) :
    (traceFormula expressions fresh steps).length≤steps*(3*gateBound+1) := by
  induction steps with
  | zero => simp [traceFormula]
  | succ steps ih =>
    have old := ih (fun time ht => bounds time (by omega))
    have last := (clauseCount_le (expressions steps)).trans (Nat.mul_le_mul_left 3 (bounds steps (by omega)))
    simp only [traceFormula,List.range_succ,List.flatMap_append,List.flatMap_singleton,List.length_append,
      atTime,List.length_map,requireTransitionExpr,compileTransitionExpr_clause_length,
      constantClauses,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul] at old ⊢
    omega

end LeanTrominoes.FiniteCNF
