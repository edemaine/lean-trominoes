/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryIndexedPresentation
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverGlobalDeduplication

/-! # Five-family presentation of exact final copied queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- Exact final copied queries for an explicit normalized clause sublist,
starting at its global final-clause index. -/
def retainedFinalIndexedClauseQueriesFrom
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (start : Nat)
    (clauses :
      List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))) :
    List RetainedFinalCopiedClauseQuery :=
  (clauses.zipIdx start).map fun taggedClause =>
    retainedFinalCopiedClauseQueryOfLiterals
      formula taggedClause.2 taggedClause.1

/-- Appending normalized clause sublists concatenates their exact queries
and shifts the second sublist by the first sublist's length. -/
theorem retainedFinalIndexedClauseQueriesFrom_append
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (start : Nat)
    (first second :
      List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))) :
    retainedFinalIndexedClauseQueriesFrom formula start (first ++ second) =
      retainedFinalIndexedClauseQueriesFrom formula start first ++
        retainedFinalIndexedClauseQueriesFrom formula
          (start + first.length) second := by
  unfold retainedFinalIndexedClauseQueriesFrom
  rw [List.zipIdx_append, List.map_append]

/-- The indexed query scan respects equality of its explicit clause list. -/
theorem retainedFinalIndexedClauseQueriesFrom_congr
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (start : Nat)
    {first second :
      List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))}
    (equal : first = second) :
    retainedFinalIndexedClauseQueriesFrom formula start first =
      retainedFinalIndexedClauseQueriesFrom formula start second := by
  subst second
  rfl

/-- The exact indexed query stream splits across the disjoint crossover
prefix and non-crossover suffix. -/
theorem retainedFinalIndexedClauseQueries_eq_crossover_append_nonCrossover
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal) :
    retainedFinalIndexedClauseQueries formula =
      retainedFinalIndexedClauseQueriesFrom formula 0
          (crossoverMetadataNormalizedClausesDedup formula) ++
      retainedFinalIndexedClauseQueriesFrom formula
          (crossoverMetadataNormalizedClausesDedup formula).length
          (nonCrossoverMetadataNormalizedClausesDedup formula) := by
  have clausesEq :=
    deduplicatedClauses_eq_named_crossover_append_nonCrossover
      formula wellFormed degree isLocal
  calc
    retainedFinalIndexedClauseQueries formula =
        retainedFinalIndexedClauseQueriesFrom formula 0
          (deduplicatedClauses formula) := by rfl
    _ = retainedFinalIndexedClauseQueriesFrom formula 0
          (crossoverMetadataNormalizedClausesDedup formula ++
            nonCrossoverMetadataNormalizedClausesDedup formula) :=
      retainedFinalIndexedClauseQueriesFrom_congr formula 0 clausesEq
    _ = _ := by
      rw [retainedFinalIndexedClauseQueriesFrom_append]
      simp only [Nat.zero_add]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
