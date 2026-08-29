/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedSourceDirectionQuery
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCopiedDirectionData

/-! # Finite data for final copied-clause queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

/-- A width-three copied clause whose directions remain as finite mixed
direct/fallback queries. -/
inductive RetainedFinalCopiedClauseQuery
  | precomputed
      (token : FormulaShapeDirectionOrdering.Token)
  | unary
      (first : LiteralProfile)
      (firstDirection : RetainedFinalCopiedSourceDirectionQuery)
  | binary
      (first : LiteralProfile)
      (firstDirection : RetainedFinalCopiedSourceDirectionQuery)
      (second : LiteralProfile)
      (secondDirection : RetainedFinalCopiedSourceDirectionQuery)
  | ternary
      (first : LiteralProfile)
      (firstDirection : RetainedFinalCopiedSourceDirectionQuery)
      (second : LiteralProfile)
      (secondDirection : RetainedFinalCopiedSourceDirectionQuery)
      (third : LiteralProfile)
      (thirdDirection : RetainedFinalCopiedSourceDirectionQuery)
  deriving DecidableEq, Fintype

instance : Inhabited RetainedFinalCopiedClauseQuery :=
  ⟨.unary default (.fallback .invalid)⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
