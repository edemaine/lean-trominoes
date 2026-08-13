/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransitionExprFormula

/-!
# Quantitative bounds for transition-expression CNF compilation

The semantic compiler is structural, so its clause count is controlled by the
number of expression nodes.  This file records the generic quantitative facts
needed to turn the bounded-machine construction into a polynomial-size CNF.
-/

namespace LeanTrominoes

namespace PeriodicCNF

namespace TransitionExpr

/-- Every expression node contributes at most three Tseitin clauses. -/
theorem clauseCount_le_three_mul_gateCount (expression : TransitionExpr) :
    expression.clauseCount ≤ 3 * expression.gateCount := by
  induction expression with
  | constant value => simp [clauseCount, gateCount]
  | wire input => simp [clauseCount, gateCount]
  | not input ih =>
      simp only [clauseCount, gateCount]
      omega
  | and first second firstIH secondIH =>
      simp only [clauseCount, gateCount]
      omega
  | or first second firstIH secondIH =>
      simp only [clauseCount, gateCount]
      omega

/-- A same-width bit-vector equality has exactly ten expression nodes per
bit, plus the terminal constant. -/
theorem vectorsEqual_gateCount_of_length_eq
    (first second : List Nat) (lengthEq : first.length = second.length) :
    (vectorsEqual first second).gateCount = 10 * first.length + 1 := by
  induction first generalizing second with
  | nil =>
      have secondNil : second = [] := List.eq_nil_of_length_eq_zero lengthEq.symm
      subst second
      rfl
  | cons first firsts ih =>
      cases second with
      | nil => simp at lengthEq
      | cons second seconds =>
          have tailLength : firsts.length = seconds.length := by
            simpa using lengthEq
          simp [vectorsEqual, equal, current, next, gateCount,
            ih seconds tailLength]
          omega

/-- Exact-one over current atoms is quadratic in the field width.  The loose
constant keeps later machine-level arithmetic simple. -/
theorem currentExactlyOne_gateCount_le (atoms : List Nat) :
    (currentExactlyOne atoms).gateCount ≤
      4 * (atoms.length + 1) ^ 2 := by
  unfold currentExactlyOne
  induction atoms with
  | nil => simp [exactlyOne, gateCount]
  | cons atom atoms ih =>
      have recurrence :
          (exactlyOne (List.map current (atom :: atoms))).gateCount =
            (exactlyOne (List.map current atoms)).gateCount +
              3 * atoms.length + 7 := by
        simp [exactlyOne, all_gateCount, current, gateCount,
          Function.comp_def]
        omega
      rw [recurrence]
      simp only [List.length_cons]
      nlinarith

/-- No-overflow succession of two same-width bit vectors has quadratic
expression size. -/
theorem binarySuccessor_gateCount_le
    (currentAtoms nextAtoms : List Nat)
    (lengthEq : currentAtoms.length = nextAtoms.length) :
    (binarySuccessor currentAtoms nextAtoms).gateCount ≤
      12 * (currentAtoms.length + 1) ^ 2 := by
  induction currentAtoms generalizing nextAtoms with
  | nil =>
      have nextNil : nextAtoms = [] :=
        List.eq_nil_of_length_eq_zero lengthEq.symm
      subst nextAtoms
      simp [binarySuccessor, gateCount]
  | cons currentAtom currentAtoms ih =>
      cases nextAtoms with
      | nil => simp at lengthEq
      | cons nextAtom nextAtoms =>
          have tailLength : currentAtoms.length = nextAtoms.length := by
            simpa using lengthEq
          have equalCount := vectorsEqual_gateCount_of_length_eq
            currentAtoms nextAtoms tailLength
          have successorBound := ih nextAtoms tailLength
          simp only [binarySuccessor, gateCount, current, next]
          rw [equalCount]
          simp only [List.length_cons]
          nlinarith

end TransitionExpr

/-- Requiring the compiled root adds exactly one unit clause. -/
@[simp]
theorem requireTransitionExpr_clause_length
    (expression : TransitionExpr) (fresh : Nat) :
    (requireTransitionExpr expression fresh).clauses.length =
      expression.clauseCount + 1 := by
  simp [requireTransitionExpr, constantClauses]

/-- The complete forced CNF has at most three clauses per expression node,
plus its final root unit clause. -/
theorem requireTransitionExpr_clause_length_le
    (expression : TransitionExpr) (fresh : Nat) :
    (requireTransitionExpr expression fresh).clauses.length ≤
      3 * expression.gateCount + 1 := by
  rw [requireTransitionExpr_clause_length]
  exact Nat.add_le_add_right expression.clauseCount_le_three_mul_gateCount 1

end PeriodicCNF

end LeanTrominoes
