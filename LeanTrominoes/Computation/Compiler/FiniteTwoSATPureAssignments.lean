/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATAssignments
import LeanTrominoes.Computation.Compiler.FiniteTwoSATControl

/-! # Polynomial word bounds for fixed arithmetic assignment lists

The exponent depends only on the finite program. The bound covers intermediate
expressions as well as every register produced by each assignment.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATExpression
open ComplexityAbstract.RAM

namespace Expr
variable {k : ℕ}

def Pure : Expr k → Prop
  | .constant _ | .inputValue _ => True
  | .load _ => False
  | .arithmetic _ a b => a.Pure ∧ b.Pure

def constants : Expr k → ℕ
  | .constant value => value.natAbs
  | .inputValue _ => 0
  | .load e => e.constants
  | .arithmetic _ a b => max a.constants b.constants

theorem pure_controlled {e : Expr k} (pure : e.Pure) {base : ℕ} (env : Fin k → ℤ)
    (memory : ℕ → ℤ) (input : List ℤ) (small : e.constants≤base)
    (registers : ∀ i, (env i).natAbs≤base) : Controlled base env memory input e := by
  induction e with
  | constant value => exact .constant value small
  | inputValue i => exact .inputValue i (registers i)
  | load e => exact False.elim pure
  | arithmetic op a b ia ib =>
    exact .arithmetic op (ia pure.1 ((le_max_left _ _).trans small))
      (ib pure.2 ((le_max_right _ _).trans small))
end Expr

namespace Assignment
variable {k : ℕ}

def exponent : List (Assignment k) → ℕ
  | [] => 1
  | a::rest => (2*a.expression.nodes+1)*exponent rest

theorem exponent_positive (xs : List (Assignment k)) : 1≤exponent xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have first : 1≤2*a.expression.nodes+1 := by omega
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

/-- One polynomial bound makes every checked expression in a fixed assignment
list safe. The input need not contain any precomputed header values. -/
theorem pure_safe {w base : ℕ} (xs : List (Assignment k)) (scratch : Fin k)
    (env : Fin k → ℤ) (memory : ℕ → ℤ) (input : List ℤ)
    (positive : 2≤base) (pure : ∀ a∈xs, a.expression.Pure)
    (constants : ∀ a∈xs, a.expression.constants≤base)
    (registers : ∀ i, (env i).natAbs≤base)
    (word : Fits w (base^exponent xs : ℕ)) (inputFits : InputFits w input) :
    Safe w scratch xs env memory := by
  induction xs generalizing base env with
  | nil =>
    exact fits_natAbs_le (by simpa only [exponent,pow_one] using word) (registers scratch)
  | cons a rest ih =>
    have controlled := a.expression.pure_controlled (pure a (by simp)) env memory input
      (constants a (by simp)) registers
    have budget := controlled.budget positive
    let nextBase := base^(2*a.expression.nodes+1)
    have growth : base≤nextBase := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤base)
        (show 1≤2*a.expression.nodes+1 by omega)
    have nextPositive : 2≤nextBase := positive.trans growth
    have wordNext : Fits w (nextBase^exponent rest : ℕ) := by
      simpa only [nextBase,← pow_mul,exponent] using word
    have budgetLe : base^(2*a.expression.nodes)≤base^exponent (a::rest) := by
      apply Nat.pow_le_pow_right (by omega)
      have expPositive := exponent_positive rest
      dsimp only [exponent]
      nlinarith
    have safe := budget.safe w (Allocation.nat_fits_le word budgetLe) inputFits
    refine ⟨safe,?_⟩
    apply ih (base:=nextBase) (env:=a.update env memory) nextPositive
      (by intro b hb; exact pure b (by simp [hb]))
      (by intro b hb; exact (constants b (by simp [hb])).trans growth)
      (by
        intro i
        simp only [update,Function.update_apply]
        split_ifs
        · exact budget.magnitude.trans (Nat.pow_le_pow_right (by omega) (by omega))
        · exact (registers i).trans growth)
      wordNext

end Assignment
end LeanTrominoes.ImplicationGraph.TwoSATExpression
