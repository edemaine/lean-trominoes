/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Complexity.FiniteTraceCNF

/-! # The finite transition compiler produces clauses of width at most three -/
namespace LeanTrominoes.FiniteCNF
open PeriodicCNF

def WidthAtMost {V : Type*} (width : Nat) (formula : Formula V) : Prop :=
  ∀ clause∈formula, clause.length≤width

theorem compiled_width (e : TransitionExpr) (fresh : Nat) :
    ∀ clause∈(compileTransitionExpr e fresh).clauses, clause.length≤3 := by
  induction e generalizing fresh with
  | constant value => simp [compileTransitionExpr,constantClauses]
  | wire input => simp [compileTransitionExpr,equalityClauses]
  | not e ih =>
    intro clause hc
    rcases List.mem_append.mp hc with old|gate
    · exact ih fresh clause old
    · simp only [notClauses,List.mem_cons,List.not_mem_nil,or_false] at gate
      rcases gate with rfl|rfl <;> simp
  | and e f ih1 ih2 =>
    intro clause hc
    simp only [compileTransitionExpr,List.mem_append] at hc
    rcases hc with (old1|old2)|gate
    · exact ih1 fresh clause old1
    · exact ih2 _ clause old2
    · simp only [andClauses,List.mem_cons,List.not_mem_nil,or_false] at gate
      rcases gate with rfl|rfl|rfl <;> simp
  | or e f ih1 ih2 =>
    intro clause hc
    simp only [compileTransitionExpr,List.mem_append] at hc
    rcases hc with (old1|old2)|gate
    · exact ih1 fresh clause old1
    · exact ih2 _ clause old2
    · simp only [orClauses,List.mem_cons,List.not_mem_nil,or_false] at gate
      rcases gate with rfl|rfl|rfl <;> simp

theorem required_width (e : TransitionExpr) (fresh : Nat) :
    ∀ clause∈(requireTransitionExpr e fresh).clauses, clause.length≤3 := by
  intro clause hc
  rcases List.mem_append.mp hc with old|root
  · exact compiled_width e fresh clause old
  · simp only [constantClauses,List.mem_singleton] at root
    subst clause; simp

theorem traceFormula_width (expressions : Nat → TransitionExpr) (fresh steps : Nat) :
    WidthAtMost 3 (traceFormula expressions fresh steps) := by
  intro clause hc
  obtain ⟨time,_,member⟩ := List.mem_flatMap.mp hc
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp member
  simpa only [List.length_map] using required_width (expressions time) fresh original ho

end LeanTrominoes.FiniteCNF
