/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapZipIdxCongr
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering

/-! # Whole-list clause-direction permutations -/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- If ordering each indexed clause applies a prescribed literal-list
permutation, then ordering the whole positioned formula maps that same
permutation over its clauses. -/
theorem orderClausesByRouteDirection_clauses_eq_map_of
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes)
    (reorder : PeriodicClause Variable → PeriodicClause Variable)
    (ordered : ∀ taggedClause ∈ source.clauses.zipIdx,
      (orderClauseByRouteDirection
        routes taggedClause.2 taggedClause.1).literals =
          reorder taggedClause.1.literals) :
    (orderClausesByRouteDirection source routes).clauses =
      source.clauses.map fun clause =>
        { position := clause.position
          literals := reorder clause.literals } := by
  unfold orderClausesByRouteDirection
  apply List.map_zipIdx_eq_map_of_mem
  intro taggedClause taggedClauseMember
  exact congrArg
    (fun literals =>
      ({ position := taggedClause.1.position
         literals := literals } : PositionedPeriodicClause Variable))
    (by
      simpa only [orderClauseByRouteDirection] using
        ordered taggedClause taggedClauseMember)

end PositionedPeriodicCNF
end LeanTrominoes
