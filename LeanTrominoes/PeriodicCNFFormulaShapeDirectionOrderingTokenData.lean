/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineRibbon
import LeanTrominoes.PeriodicCNFUnaryProgramClauseProfileData

/-! # Finite tokens for direction-aware formula shapes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeDirectionOrdering

open UnaryProgramClauseProfile

/-- A width-three clause profile together with the finite first direction of
each corresponding incidence route. -/
inductive DirectedClauseProfile
  | unary (first : LiteralProfile) (firstDirection : AxisDirection)
  | binary
      (first : LiteralProfile) (firstDirection : AxisDirection)
      (second : LiteralProfile) (secondDirection : AxisDirection)
  | ternary
      (first : LiteralProfile) (firstDirection : AxisDirection)
      (second : LiteralProfile) (secondDirection : AxisDirection)
      (third : LiteralProfile) (thirdDirection : AxisDirection)
  deriving DecidableEq, Fintype

instance : Inhabited DirectedClauseProfile :=
  ⟨.unary default .invalid⟩

/-- Finite input alphabet for a direction-aware formula shape. -/
inductive Token
  | clause (profile : DirectedClauseProfile)
  | variable
  deriving DecidableEq, Fintype, Inhabited

end FormulaShapeDirectionOrdering
end PeriodicCNF
end LeanTrominoes
