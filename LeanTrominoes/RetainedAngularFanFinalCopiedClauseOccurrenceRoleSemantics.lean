/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingData
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseOccurrenceRoleCompiler

/-! # Arity semantics of final copied-clause occurrence roles -/

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeDirectionOrdering

/-- Number of literal occurrences represented by one direction descriptor. -/
def retainedFinalCopiedDescriptorArity :
    PeriodicCNF.FormulaShapeDirectionOrdering.Token → Nat
  | .clause profile => profile.taggedLiterals.length
  | .variable => 0

@[simp] theorem retainedFinalCopiedDescriptorArity_clause_unary
    (first direction) :
    retainedFinalCopiedDescriptorArity
        (.clause (.unary first direction)) = 1 :=
  rfl

@[simp] theorem retainedFinalCopiedDescriptorArity_clause_binary
    (first firstDirection second secondDirection) :
    retainedFinalCopiedDescriptorArity
        (.clause (.binary first firstDirection second secondDirection)) = 2 :=
  rfl

@[simp] theorem retainedFinalCopiedDescriptorArity_clause_ternary
    (first firstDirection second secondDirection third thirdDirection) :
    retainedFinalCopiedDescriptorArity
        (.clause (.ternary first firstDirection second secondDirection
          third thirdDirection)) = 3 :=
  rfl

@[simp] theorem retainedFinalCopiedDescriptorArity_variable :
    retainedFinalCopiedDescriptorArity .variable = 0 :=
  rfl

/-- Query arity is preserved by the fixed query evaluator. -/
@[simp] theorem retainedFinalCopiedClauseQueryArity_eq_descriptor
    (query : RetainedFinalCopiedClauseQuery) :
    retainedFinalCopiedClauseQueryArity query =
      retainedFinalCopiedDescriptorArity
        (retainedFinalCopiedClauseDescriptorOfQuery query) := by
  cases query with
  | precomputed token => cases token with
    | clause profile => cases profile <;> rfl
    | _ => rfl
  | unary => rfl
  | binary => rfl
  | ternary => rfl

/-- Finite arity expansion emits exactly the query's represented number of
literal roles. -/
@[simp] theorem retainedFinalCopiedClauseOccurrenceRolesOfQuery_length
    (query : RetainedFinalCopiedClauseQuery) :
    (retainedFinalCopiedClauseOccurrenceRolesOfQuery query).length =
      retainedFinalCopiedClauseQueryArity query := by
  cases query with
  | precomputed token => cases token with
    | clause profile => cases profile <;> rfl
    | _ => rfl
  | unary => rfl
  | binary => rfl
  | ternary => rfl

/-- The occurrence-role stream length is the sum of evaluated descriptor
arities. -/
theorem retainedFinalCopiedClauseOccurrenceRoles_length
    (queries : List RetainedFinalCopiedClauseQuery) :
    (retainedFinalCopiedClauseOccurrenceRoles queries).length =
      ((retainedFinalCopiedClauseDescriptors queries).map
        retainedFinalCopiedDescriptorArity).sum := by
  induction queries with
  | nil => rfl
  | cons query queries induction =>
      simp only [retainedFinalCopiedClauseOccurrenceRoles,
        retainedFinalCopiedClauseDescriptors, List.flatMap_cons,
        List.length_append, List.map_append, List.sum_append,
        retainedFinalCopiedClauseOccurrenceRolesOfQuery_length,
        List.map_singleton, List.sum_singleton,
        retainedFinalCopiedClauseQueryArity_eq_descriptor]
      exact congrArg
        (fun value =>
          retainedFinalCopiedDescriptorArity
              (retainedFinalCopiedClauseDescriptorOfQuery query) + value)
        induction

end LeanTrominoes.PeriodicEightOccurrenceSplit
