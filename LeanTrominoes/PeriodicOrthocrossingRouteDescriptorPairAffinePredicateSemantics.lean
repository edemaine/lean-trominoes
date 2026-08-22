/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicates
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineSemantics

/-! # Exact tagged-token semantics of affine pair predicates -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- One affine comparison has the same value on a canonical tagged block as
on the descriptor pair that generated it. -/
theorem Atom.eval_tokens_eq_pair
    (atom : Atom) (pair : RouteDescriptor × RouteDescriptor) :
    atom.eval (tokenFieldValue (descriptorPairTokens pair)) =
      atom.eval (pairFieldValue pair) := by
  unfold Atom.eval
  change atom.relation.eval
      (atom.first.evalTokens (descriptorPairTokens pair))
      (atom.second.evalTokens (descriptorPairTokens pair)) =
    atom.relation.eval (atom.first.evalPair pair) (atom.second.evalPair pair)
  rw [Expression.evalTokens_descriptorPairTokens atom.first pair,
    Expression.evalTokens_descriptorPairTokens atom.second pair]

/-- Every fixed Boolean formula over affine comparisons is preserved exactly
by the pair-field tagger. -/
theorem Predicate.evalTokens_descriptorPairTokens
    (predicate : Predicate) (pair : RouteDescriptor × RouteDescriptor) :
    predicate.evalTokens (descriptorPairTokens pair) =
      predicate.evalPair pair := by
  unfold Predicate.evalTokens Predicate.evalPair
  induction predicate with
  | truth | falsity => rfl
  | atom comparison =>
      exact Atom.eval_tokens_eq_pair comparison pair
  | conjunction first second firstInduction secondInduction =>
      simp only [Predicate.eval]
      rw [firstInduction, secondInduction]
  | disjunction first second firstInduction secondInduction =>
      simp only [Predicate.eval]
      rw [firstInduction, secondInduction]
  | negation input induction =>
      simp only [Predicate.eval]
      rw [induction]

@[simp] theorem eval_constant
    (valuation : Side → Fin 11 → Nat) (value : Int) :
    (constant value).eval valuation = value := by
  simp [constant, Expression.eval]

@[simp] theorem eval_field
    (valuation : Side → Fin 11 → Nat) (side : Side) (position : Fin 11) :
    (field side position).eval valuation = valuation side position := by
  simp [field, Expression.eval, Term.eval, term]

@[simp] theorem eval_all
    (valuation : Side → Fin 11 → Nat) (predicates : List Predicate) :
    (all predicates).eval valuation =
      predicates.all (Predicate.eval valuation) := by
  induction predicates with
  | nil => rfl
  | cons predicate predicates induction =>
      simp [all, Predicate.eval, induction]

@[simp] theorem eval_any
    (valuation : Side → Fin 11 → Nat) (predicates : List Predicate) :
    (any predicates).eval valuation =
      predicates.any (Predicate.eval valuation) := by
  induction predicates with
  | nil => rfl
  | cons predicate predicates induction =>
      simp [any, Predicate.eval, induction]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
