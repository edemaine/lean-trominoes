/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCopiedDirectionData

/-! # Literal-list extensionality of final copied-clause profiles -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicOrthocrossing

/-- The route-based copied profile depends on a positioned clause only
through its literal list. -/
theorem routedCopiedClauseProfile_eq_of_literals_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (first second : PositionedPeriodicClause
      (WrappedPeriodicPlanarSATVariable Variable))
    (literalsEq : first.literals = second.literals) :
    routedCopiedClauseProfile source clauseIndex first =
      routedCopiedClauseProfile source clauseIndex second := by
  cases first with
  | mk firstPosition firstLiterals =>
      cases second with
      | mk secondPosition secondLiterals =>
          change firstLiterals = secondLiterals at literalsEq
          subst secondLiterals
          rfl

/-- The finite copied profile has the same literal-list extensionality. -/
theorem copiedClauseProfile_eq_of_literals_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (first second : PositionedPeriodicClause
      (WrappedPeriodicPlanarSATVariable Variable))
    (literalsEq : first.literals = second.literals) :
    copiedClauseProfile source clauseIndex first =
      copiedClauseProfile source clauseIndex second := by
  cases first with
  | mk firstPosition firstLiterals =>
      cases second with
      | mk secondPosition secondLiterals =>
          change firstLiterals = secondLiterals at literalsEq
          subst secondLiterals
          rfl

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
