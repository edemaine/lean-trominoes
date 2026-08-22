/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineAtomBatchCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineSignedCountSemantics

/-! # Ordered atom semantics for batched affine predicates -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open DelimitedBinaryWordPairLengthComparisonMachine

/-- The signed-total ordering belonging to one atom on tagged fields. -/
def Atom.tokenOrdering
    (atom : Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) : LengthOrdering :=
  let counts := atom.difference.tokenCounts tokens
  compareNats counts.1 counts.2

/-- Interpreting the atom's signed-total ordering gives its exact semantic
truth value. -/
@[simp] theorem Atom.acceptsOrdering_tokenOrdering
    (atom : Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    atom.relation.acceptsOrdering (atom.tokenOrdering tokens) =
      atom.eval (tokenFieldValue tokens) := by
  have exact := atom.evalFromTokenCounts_eq_eval tokens
  simpa only [Atom.tokenOrdering, Atom.evalFromTokenCounts] using exact

/-- Atoms in left-to-right evaluation order. -/
def Predicate.atoms : Predicate → List Atom
  | .truth | .falsity => []
  | .atom comparison => [comparison]
  | .conjunction first second | .disjunction first second =>
      first.atoms ++ second.atoms
  | .negation input => input.atoms

/-- Exact ordering list belonging to one predicate. -/
def Predicate.tokenOrderings
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    Predicate → List LengthOrdering
  | .truth | .falsity => []
  | .atom comparison => [comparison.tokenOrdering tokens]
  | .conjunction first second | .disjunction first second =>
      first.tokenOrderings tokens ++ second.tokenOrderings tokens
  | .negation input => input.tokenOrderings tokens

/-- Consume one ordering per atom while evaluating a predicate.  Malformed
short words use `false` for a missing atom; exact batch words never take that
branch. -/
def Predicate.evalOrderings :
    Predicate → List LengthOrdering → Bool × List LengthOrdering
  | .truth, orderings => (true, orderings)
  | .falsity, orderings => (false, orderings)
  | .atom _, [] => (false, [])
  | .atom comparison, ordering :: orderings =>
      (comparison.relation.acceptsOrdering ordering, orderings)
  | .conjunction first second, orderings =>
      let firstResult := first.evalOrderings orderings
      let secondResult := second.evalOrderings firstResult.2
      (firstResult.1 && secondResult.1, secondResult.2)
  | .disjunction first second, orderings =>
      let firstResult := first.evalOrderings orderings
      let secondResult := second.evalOrderings firstResult.2
      (firstResult.1 || secondResult.1, secondResult.2)
  | .negation input, orderings =>
      let result := input.evalOrderings orderings
      (!result.1, result.2)

/-- A predicate consumes exactly its own atom-ordering prefix and returns its
tagged-field semantic value, leaving every supplied suffix untouched. -/
theorem Predicate.evalOrderings_tokenOrderings_append
    (predicate : Predicate)
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (suffix : List LengthOrdering) :
    predicate.evalOrderings (predicate.tokenOrderings tokens ++ suffix) =
      (predicate.evalTokens tokens, suffix) := by
  induction predicate generalizing suffix with
  | truth | falsity => rfl
  | atom comparison =>
      unfold Predicate.tokenOrderings Predicate.evalOrderings
        Predicate.evalTokens Predicate.eval
      simp only [List.singleton_append]
      rw [comparison.acceptsOrdering_tokenOrdering]
  | conjunction first second firstInduction secondInduction =>
      unfold Predicate.tokenOrderings
      rw [List.append_assoc]
      unfold Predicate.evalOrderings
      rw [firstInduction]
      dsimp only
      rw [secondInduction]
      rfl
  | disjunction first second firstInduction secondInduction =>
      unfold Predicate.tokenOrderings
      rw [List.append_assoc]
      unfold Predicate.evalOrderings
      rw [firstInduction]
      dsimp only
      rw [secondInduction]
      rfl
  | negation input induction =>
      unfold Predicate.tokenOrderings
      unfold Predicate.evalOrderings
      rw [induction]
      rfl

/-- Flattened atom list for several predicates in evaluation order. -/
def predicateListAtoms (predicates : List Predicate) : List Atom :=
  predicates.flatMap Predicate.atoms

/-- Flattened exact ordering word for several predicates. -/
def predicateListTokenOrderings
    (predicates : List Predicate)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List LengthOrdering :=
  predicates.flatMap fun predicate => predicate.tokenOrderings tokens

/-- Sequentially consume and evaluate a list of predicates. -/
def evalPredicateListOrderings :
    List Predicate → List LengthOrdering →
      List Bool × List LengthOrdering
  | [], orderings => ([], orderings)
  | predicate :: predicates, orderings =>
      let firstResult := predicate.evalOrderings orderings
      let restResult := evalPredicateListOrderings predicates firstResult.2
      (firstResult.1 :: restResult.1, restResult.2)

/-- A predicate list consumes exactly its flattened atom-ordering prefix and
returns all tagged-field truth values in order. -/
theorem evalPredicateListOrderings_tokenOrderings_append
    (predicates : List Predicate)
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (suffix : List LengthOrdering) :
    evalPredicateListOrderings predicates
        (predicateListTokenOrderings predicates tokens ++ suffix) =
      (predicates.map fun predicate => predicate.evalTokens tokens, suffix) := by
  induction predicates generalizing suffix with
  | nil => rfl
  | cons predicate predicates induction =>
      unfold predicateListTokenOrderings
      rw [List.flatMap_cons, List.append_assoc]
      unfold evalPredicateListOrderings
      rw [predicate.evalOrderings_tokenOrderings_append]
      dsimp only
      change
        (predicate.evalTokens tokens ::
            (evalPredicateListOrderings predicates
              (predicateListTokenOrderings predicates tokens ++ suffix)).1,
          (evalPredicateListOrderings predicates
            (predicateListTokenOrderings predicates tokens ++ suffix)).2) =
          (predicate.evalTokens tokens ::
            predicates.map (fun remaining =>
              remaining.evalTokens tokens), suffix)
      rw [induction]

/-- Flattening the atom syntax and then taking token orderings agrees with
the structurally recursive ordering word. -/
theorem Predicate.atoms_map_tokenOrdering
    (predicate : Predicate)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    predicate.atoms.map (fun atom => atom.tokenOrdering tokens) =
      predicate.tokenOrderings tokens := by
  induction predicate with
  | truth | falsity | atom => rfl
  | conjunction first second firstInduction secondInduction =>
      unfold Predicate.atoms Predicate.tokenOrderings
      rw [List.map_append, firstInduction, secondInduction]
  | disjunction first second firstInduction secondInduction =>
      unfold Predicate.atoms Predicate.tokenOrderings
      rw [List.map_append, firstInduction, secondInduction]
  | negation input induction =>
      unfold Predicate.atoms Predicate.tokenOrderings
      exact induction

/-- The batched atom list is exactly the concatenation used by the predicate
ordering interpreter. -/
theorem predicateListAtoms_map_tokenOrdering
    (predicates : List Predicate)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (predicateListAtoms predicates).map
        (fun atom => atom.tokenOrdering tokens) =
      predicateListTokenOrderings predicates tokens := by
  unfold predicateListAtoms predicateListTokenOrderings
  induction predicates with
  | nil => rfl
  | cons predicate predicates induction =>
      simp only [List.flatMap_cons, List.map_append]
      rw [predicate.atoms_map_tokenOrdering, induction]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
