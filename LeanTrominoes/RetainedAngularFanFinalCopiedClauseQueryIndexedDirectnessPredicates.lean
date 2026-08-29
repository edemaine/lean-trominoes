/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryIndexedAllDirectChoices

/-! # Predicates for indexed final-query directness -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Every packed query in an explicitly indexed clause family is direct.

The structure wrapper keeps large concrete clause families opaque while this
fact is transported through later semantic layers. -/
structure FinalIndexedClauseQueriesAllDirect
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (start : Nat)
    (clauses :
      List (PeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))) : Prop where
  allDirect : ∀ query ∈ retainedFinalIndexedClauseQueriesFrom
    formula start clauses, query.AllDirect

/-- Every literal of an explicitly indexed clause family has a successful
final direct route choice.  This is wrapped for the same opacity reason as
`FinalIndexedClauseQueriesAllDirect`. -/
structure FinalIndexedClauseRouteChoices
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (start : Nat)
    (clauses :
      List (PeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))) : Prop where
  choices : ∀ taggedClause ∈ clauses.zipIdx start,
    ∀ taggedLiteral ∈ taggedClause.1.zipIdx,
      ∃ choice,
        retainedFinalDirectSourceRouteChoice?
            formula taggedClause.2 taggedLiteral.2 =
          some choice

/-- All-direct queries over nonempty width-three clauses provide successful
choices throughout the indexed family. -/
theorem finalIndexedClauseRouteChoices_of_allDirect
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (start : Nat)
    (clauses :
      List (PeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)))
    (nonempty : ∀ clause ∈ clauses, clause ≠ [])
    (width : ∀ clause ∈ clauses, clause.length ≤ 3)
    (allDirect :
      FinalIndexedClauseQueriesAllDirect formula start clauses) :
    FinalIndexedClauseRouteChoices formula start clauses := by
  exact ⟨retainedFinalIndexedClauseQueriesFrom_choices_of_allDirect
    formula start clauses nonempty width allDirect.allDirect⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
