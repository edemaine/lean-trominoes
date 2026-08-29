/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryIndexedAllDirectChoices
import LeanTrominoes.RetainedAngularFanFinalDirectClauseTerminalColumnIndexedSemantics

/-! # All-direct semantics of final terminal columns -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- If every packed query in a nonempty width-three indexed family is
direct, its emitted terminal column is the actual unscaled column. -/
theorem retainedFinalDirectTerminalCoordinates_indexedFrom_eq_actual_of_allDirect
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (start : Nat)
    (clauses :
      List (PeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)))
    (nonempty : ∀ clause ∈ clauses, clause ≠ [])
    (width : ∀ clause ∈ clauses, clause.length ≤ 3)
    (allDirect : ∀ query ∈
      retainedFinalIndexedClauseQueriesFrom formula start clauses,
        query.AllDirect) :
    retainedFinalDirectTerminalCoordinates
        (retainedFinalIndexedClauseQueriesFrom
          formula start clauses) =
      retainedFinalTerminalCoordinatesFrom
        (finalCoordinatedSourceRoutes formula) start clauses :=
  retainedFinalDirectTerminalCoordinates_indexedFrom_eq_actual
    formula start clauses width
    (retainedFinalIndexedClauseQueriesFrom_choices_of_allDirect
      formula start clauses nonempty width allDirect)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
