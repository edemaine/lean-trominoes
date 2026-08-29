/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryIndexedDirectnessPredicates
import LeanTrominoes.RetainedAngularFanFinalDirectClauseTerminalColumnIndexedSemantics

/-! # Terminal-column semantics from indexed route choices -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Successful choices throughout a width-three indexed family identify its
direct query column with the actual unscaled terminal coordinates. -/
theorem retainedFinalDirectTerminalCoordinates_indexedFrom_eq_actual_of_routeChoices
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (start : Nat)
    (clauses :
      List (PeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)))
    (width : ∀ clause ∈ clauses, clause.length ≤ 3)
    (choices : FinalIndexedClauseRouteChoices
      formula start clauses) :
    retainedFinalDirectTerminalCoordinates
        (retainedFinalIndexedClauseQueriesFrom
          formula start clauses) =
      retainedFinalTerminalCoordinatesFrom
        (finalCoordinatedSourceRoutes formula) start clauses :=
  retainedFinalDirectTerminalCoordinates_indexedFrom_eq_actual
    formula start clauses width choices.choices

end PeriodicEightOccurrenceSplit
end LeanTrominoes
