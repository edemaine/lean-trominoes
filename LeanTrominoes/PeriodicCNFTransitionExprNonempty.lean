/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransitionExprFormula

/-! # Nonempty clauses from transition-expression compilation -/

namespace LeanTrominoes
namespace PeriodicCNF

theorem compileTransitionExpr_clauses_nonempty
    (expression : TransitionExpr) (fresh : Nat) :
    ∀ clause ∈ (compileTransitionExpr expression fresh).clauses,
      clause ≠ [] := by
  induction expression generalizing fresh with
  | constant value =>
      simp [compileTransitionExpr, constantClauses]
  | wire input =>
      simp [compileTransitionExpr, equalityClauses]
  | not input induction =>
      intro clause member
      simp only [compileTransitionExpr, List.mem_append] at member
      rcases member with compiled | gate
      · exact induction fresh clause compiled
      · simp only [notClauses, List.mem_cons, List.not_mem_nil,
          or_false] at gate
        rcases gate with rfl | rfl <;> simp
  | and first second firstIH secondIH =>
      intro clause member
      simp only [compileTransitionExpr, List.mem_append] at member
      rcases member with previous | gate
      · rcases previous with inFirst | inSecond
        · exact firstIH fresh clause inFirst
        · exact secondIH
            (compileTransitionExpr first fresh).nextFresh clause inSecond
      · simp only [andClauses, List.mem_cons, List.not_mem_nil,
          or_false] at gate
        rcases gate with rfl | rfl | rfl <;> simp
  | or first second firstIH secondIH =>
      intro clause member
      simp only [compileTransitionExpr, List.mem_append] at member
      rcases member with previous | gate
      · rcases previous with inFirst | inSecond
        · exact firstIH fresh clause inFirst
        · exact secondIH
            (compileTransitionExpr first fresh).nextFresh clause inSecond
      · simp only [orClauses, List.mem_cons, List.not_mem_nil,
          or_false] at gate
        rcases gate with rfl | rfl | rfl <;> simp

/-- Every Tseitin clause, including the final forced-root unit clause, is
nonempty. -/
theorem requireTransitionExpr_clauses_nonempty
    (expression : TransitionExpr) (fresh : Nat) :
    ∀ clause ∈ (requireTransitionExpr expression fresh).clauses,
      clause ≠ [] := by
  intro clause member
  unfold requireTransitionExpr at member
  rw [List.mem_append] at member
  rcases member with compiled | root
  · exact compileTransitionExpr_clauses_nonempty
      expression fresh clause compiled
  · simp only [constantClauses, List.mem_singleton] at root
    subst clause
    simp

end PeriodicCNF
end LeanTrominoes
