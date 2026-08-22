/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineAlgebraSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineSignedCounts
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorUnarySemantics

/-! # Exact semantics of signed affine unary totals -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open DelimitedBinaryWordPairLengthComparisonMachine

/-- Splitting one signed coefficient into natural positive and negative
contributions preserves its evaluated integer term. -/
theorem Term.signedOfUnaryFields_counts
    (valuation : Side → Fin 11 → Nat) (expressionTerm : Term) :
    signedOfUnaryFields
        (expressionTerm.positiveCount valuation)
        (expressionTerm.negativeCount valuation) =
      expressionTerm.eval valuation := by
  unfold Term.positiveCount Term.negativeCount Term.eval
    signedOfUnaryFields
  simp only [Int.natCast_mul]
  rw [← sub_mul]
  have coefficientEq :
      (expressionTerm.coefficient.toNat : Int) -
          ((-expressionTerm.coefficient).toNat : Int) =
        expressionTerm.coefficient := by
    exact signedOfUnaryFields_signedUnaryFields
      expressionTerm.coefficient
  rw [coefficientEq]

/-- Positive-minus-negative totals of a term list equal the sum of the
corresponding signed affine terms. -/
theorem Term.signedOfUnaryFields_sum_counts
    (valuation : Side → Fin 11 → Nat) (terms : List Term) :
    signedOfUnaryFields
        (terms.map (Term.positiveCount valuation)).sum
        (terms.map (Term.negativeCount valuation)).sum =
      (terms.map (Term.eval valuation)).sum := by
  induction terms with
  | nil => rfl
  | cons expressionTerm terms induction =>
      simp only [List.map_cons, List.sum_cons, signedOfUnaryFields]
      simp only [Int.natCast_add]
      have termEq :
        ((expressionTerm.positiveCount valuation : Nat) : Int) -
            (expressionTerm.negativeCount valuation : Nat) =
          expressionTerm.eval valuation := by
        exact expressionTerm.signedOfUnaryFields_counts valuation
      have tailEq :
        (((terms.map (Term.positiveCount valuation)).sum : Nat) : Int) -
            ((terms.map (Term.negativeCount valuation)).sum : Nat) =
          (terms.map (Term.eval valuation)).sum := by
        exact induction
      omega

/-- Positive-minus-negative totals recover the exact signed affine value. -/
theorem Expression.signedOfUnaryFields_counts
    (valuation : Side → Fin 11 → Nat) (expression : Expression) :
    signedOfUnaryFields
        (expression.positiveCount valuation)
        (expression.negativeCount valuation) =
      expression.eval valuation := by
  unfold Expression.positiveCount Expression.negativeCount
    Expression.eval signedOfUnaryFields
  simp only [Int.natCast_add]
  have constantEq :
    (expression.constant.toNat : Int) -
        ((-expression.constant).toNat : Int) = expression.constant := by
    exact signedOfUnaryFields_signedUnaryFields expression.constant
  have termsEq :
    (((expression.terms.map
          (Term.positiveCount valuation)).sum : Nat) : Int) -
        ((expression.terms.map
          (Term.negativeCount valuation)).sum : Nat) =
      (expression.terms.map (Term.eval valuation)).sum := by
    exact Term.signedOfUnaryFields_sum_counts valuation expression.terms
  omega

/-- The three length-comparison outcomes characterize the corresponding
natural-number relations. -/
theorem compareNats_eq_less_iff (first second : Nat) :
    compareNats first second = .less ↔ first < second := by
  induction first generalizing second with
  | zero => cases second <;> simp [compareNats]
  | succ first induction =>
      cases second with
      | zero => simp [compareNats]
      | succ second => simpa [compareNats] using induction second

theorem compareNats_eq_equal_iff (first second : Nat) :
    compareNats first second = .equal ↔ first = second := by
  induction first generalizing second with
  | zero => cases second <;> simp [compareNats]
  | succ first induction =>
      cases second with
      | zero => simp [compareNats]
      | succ second => simpa [compareNats] using induction second

theorem compareNats_eq_greater_iff (first second : Nat) :
    compareNats first second = .greater ↔ second < first := by
  induction first generalizing second with
  | zero => cases second <;> simp [compareNats]
  | succ first induction =>
      cases second with
      | zero => simp [compareNats]
      | succ second => simpa [compareNats] using induction second

/-- Interpreting the length ordering of two natural totals is exactly the
corresponding signed-integer comparison against zero. -/
theorem Relation.acceptsOrdering_compareNats
    (relation : Relation) (positive negative : Nat) :
    relation.acceptsOrdering (compareNats positive negative) =
      relation.eval (signedOfUnaryFields positive negative) 0 := by
  cases ordering : compareNats positive negative with
  | less =>
      have order := (compareNats_eq_less_iff positive negative).mp ordering
      cases relation <;>
        simp [Relation.acceptsOrdering, Relation.eval,
          signedOfUnaryFields] <;> omega
  | equal =>
      have order := (compareNats_eq_equal_iff positive negative).mp ordering
      cases relation <;>
        simp [Relation.acceptsOrdering, Relation.eval,
          signedOfUnaryFields, order]
  | greater =>
      have order :=
        (compareNats_eq_greater_iff positive negative).mp ordering
      cases relation <;>
        simp [Relation.acceptsOrdering, Relation.eval,
          signedOfUnaryFields] <;> omega

/-- Count-based evaluation of one affine atom on tagged unary fields is exact. -/
theorem Atom.evalFromTokenCounts_eq_eval
    (atom : Atom) (tokens : List RouteDescriptorPairFieldTags.Token) :
    atom.evalFromTokenCounts tokens = atom.eval (tokenFieldValue tokens) := by
  unfold Atom.evalFromTokenCounts Expression.tokenCounts Atom.difference
  rw [Relation.acceptsOrdering_compareNats]
  rw [Expression.signedOfUnaryFields_counts]
  rw [Expression.eval_subtract]
  unfold Atom.eval
  cases atom.relation <;> simp [Relation.eval] <;> omega

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
