/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCoordinatedSourceClauses

/-! # Recovering positioned final clauses from literal-list lookups -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- A lookup in the duplicate-free final literal presentation recovers the
positioned final clause stored at the same index. -/
theorem exists_finalCoordinatedPositionedClause_of_lookup
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (lookup :
      (deduplicatedClauses formula)[clauseIndex]? = some clause) :
    ∃ positionedClause : PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable),
      (finalCoordinatedSource formula).clauses[clauseIndex]? =
          some positionedClause ∧
        positionedClause.literals = clause := by
  have mappedLookup :
      ((finalCoordinatedSource formula).clauses.map
          PositionedPeriodicClause.literals)[clauseIndex]? =
        some clause := by
    rw [finalCoordinatedSource_clauseLiterals_eq]
    exact lookup
  rw [List.getElem?_map, Option.map_eq_some_iff] at mappedLookup
  exact mappedLookup

end PeriodicEightOccurrenceSplit
end LeanTrominoes
