/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQuery
import LeanTrominoes.RetainedAngularFanFinalCoordinatedSourceClauses

/-! # Indexed normalized-clause presentation of final copied queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- Final copied queries indexed directly over the duplicate-free normalized
literal lists, retaining their existing presentation indices. -/
def retainedFinalIndexedClauseQueries
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List RetainedFinalCopiedClauseQuery :=
  (deduplicatedClauses formula).zipIdx.map fun taggedClause =>
    retainedFinalCopiedClauseQueryOfLiterals
      formula taggedClause.2 taggedClause.1

/-- Forgetting final clause positions turns the public query stream into the
same stable indexed map over duplicate-free normalized literal lists. -/
theorem retainedFinalCopiedClauseQueries_eq_indexed
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    retainedFinalCopiedClauseQueries formula =
      retainedFinalIndexedClauseQueries formula := by
  unfold retainedFinalCopiedClauseQueries
    retainedFinalIndexedClauseQueries retainedFinalCopiedClauseQuery
  let sourceClauses := (finalCoordinatedSource formula).clauses
  let literals :
      PositionedPeriodicClause
          (WrappedPeriodicPlanarSATVariable Variable) →
        PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) :=
    PositionedPeriodicClause.literals
  let query : Nat →
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) →
        RetainedFinalCopiedClauseQuery :=
    retainedFinalCopiedClauseQueryOfLiterals formula
  change sourceClauses.zipIdx.map (fun taggedClause =>
      query taggedClause.2 (literals taggedClause.1)) = _
  calc
    sourceClauses.zipIdx.map (fun taggedClause =>
          query taggedClause.2 (literals taggedClause.1)) =
        ((sourceClauses.map literals).zipIdx).map
          (fun taggedClause => query taggedClause.2 taggedClause.1) := by
      rw [List.zipIdx_map, List.map_map]
      rfl
    _ = (deduplicatedClauses formula).zipIdx.map
          (fun taggedClause => query taggedClause.2 taggedClause.1) := by
      exact congrArg
        (fun clauses => clauses.zipIdx.map
          (fun taggedClause => query taggedClause.2 taggedClause.1))
        (finalCoordinatedSource_clauseLiterals_eq formula)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
