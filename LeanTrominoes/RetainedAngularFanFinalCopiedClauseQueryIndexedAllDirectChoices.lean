/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryAllDirectChoice

/-! # Route choices from indexed all-direct final clause queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- All-direct packed queries recover successful route choices throughout
their nonempty width-three indexed clause family. -/
theorem retainedFinalIndexedClauseQueriesFrom_choices_of_allDirect
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
    ∀ taggedClause ∈ clauses.zipIdx start,
      ∀ taggedLiteral ∈ taggedClause.1.zipIdx,
        ∃ choice,
          retainedFinalDirectSourceRouteChoice?
              formula taggedClause.2 taggedLiteral.2 =
            some choice := by
  intro taggedClause taggedClauseMember
  apply retainedFinalCopiedClauseQueryOfLiterals_choices_of_allDirect
    formula taggedClause.2 taggedClause.1
  · exact nonempty taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember)
  · exact width taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember)
  · apply allDirect
    unfold retainedFinalIndexedClauseQueriesFrom
    exact List.mem_map.mpr
      ⟨taggedClause, taggedClauseMember, rfl⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
