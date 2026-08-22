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

@[simp] theorem Expression.evalPair_constant
    (value : Int) (pair : RouteDescriptor × RouteDescriptor) :
    (RouteDescriptorPairAffine.constant value).evalPair pair = value :=
  eval_constant (pairFieldValue pair) value

@[simp] theorem Predicate.evalPair_truth
    (pair : RouteDescriptor × RouteDescriptor) :
    Predicate.truth.evalPair pair = true :=
  rfl

@[simp] theorem Predicate.evalPair_falsity
    (pair : RouteDescriptor × RouteDescriptor) :
    Predicate.falsity.evalPair pair = false :=
  rfl

@[simp] theorem Predicate.evalPair_conjunction
    (first second : Predicate) (pair : RouteDescriptor × RouteDescriptor) :
    (Predicate.conjunction first second).evalPair pair =
      (first.evalPair pair && second.evalPair pair) :=
  rfl

@[simp] theorem Predicate.evalPair_disjunction
    (first second : Predicate) (pair : RouteDescriptor × RouteDescriptor) :
    (Predicate.disjunction first second).evalPair pair =
      (first.evalPair pair || second.evalPair pair) :=
  rfl

@[simp] theorem Predicate.evalPair_negation
    (input : Predicate) (pair : RouteDescriptor × RouteDescriptor) :
    (Predicate.negation input).evalPair pair = !input.evalPair pair :=
  rfl

@[simp] theorem evalPair_equal
    (first second : Expression) (pair : RouteDescriptor × RouteDescriptor) :
    (equal first second).evalPair pair =
      decide (first.evalPair pair = second.evalPair pair) :=
  rfl

@[simp] theorem evalPair_notEqual
    (first second : Expression) (pair : RouteDescriptor × RouteDescriptor) :
    (notEqual first second).evalPair pair =
      decide (first.evalPair pair ≠ second.evalPair pair) :=
  rfl

@[simp] theorem evalPair_less
    (first second : Expression) (pair : RouteDescriptor × RouteDescriptor) :
    (less first second).evalPair pair =
      decide (first.evalPair pair < second.evalPair pair) :=
  rfl

@[simp] theorem evalPair_lessEqual
    (first second : Expression) (pair : RouteDescriptor × RouteDescriptor) :
    (lessEqual first second).evalPair pair =
      decide (first.evalPair pair ≤ second.evalPair pair) :=
  rfl

@[simp] theorem eval_all
    (valuation : Side → Fin 11 → Nat) (predicates : List Predicate) :
    (all predicates).eval valuation =
      predicates.all (Predicate.eval valuation) := by
  induction predicates with
  | nil => rfl
  | cons predicate predicates induction =>
      simp [all, Predicate.eval, induction]

@[simp] theorem evalPair_all
    (predicates : List Predicate) (pair : RouteDescriptor × RouteDescriptor) :
    (all predicates).evalPair pair =
      predicates.all (fun predicate => predicate.evalPair pair) := by
  exact eval_all (pairFieldValue pair) predicates

@[simp] theorem eval_any
    (valuation : Side → Fin 11 → Nat) (predicates : List Predicate) :
    (any predicates).eval valuation =
      predicates.any (Predicate.eval valuation) := by
  induction predicates with
  | nil => rfl
  | cons predicate predicates induction =>
      simp [any, Predicate.eval, induction]

@[simp] theorem evalPair_any
    (predicates : List Predicate) (pair : RouteDescriptor × RouteDescriptor) :
    (any predicates).evalPair pair =
      predicates.any (fun predicate => predicate.evalPair pair) := by
  exact eval_any (pairFieldValue pair) predicates

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
