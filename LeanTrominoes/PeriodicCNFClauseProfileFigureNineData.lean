/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFUnaryProgramClauseProfileData

/-! # Finite clause arities after the Figure 9 transformations -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace ClauseProfileFigureNine

open UnaryProgramClauseArity
open UnaryProgramClauseProfile

/-- Arity sequence produced by the Figure 9 disjunction gadget before unit
clauses are eliminated. -/
def oneInThreeArities : ClauseProfile → List Arity
  | .unary _ => [.ternary, .ternary, .ternary, .unary, .unary]
  | .binary _ _ => [.ternary, .ternary, .ternary, .unary]
  | .ternary _ _ _ => [.ternary, .ternary, .ternary]

/-- Arity sequence produced while eliminating one exact-one clause. -/
def noUnitArities : Arity → List Arity
  | .unary => [.ternary, .binary]
  | .binary => [.binary]
  | .ternary => [.ternary]

/-- Final unit-free arities contributed by one guarded source clause. -/
def clauseArities (profile : ClauseProfile) : List Arity :=
  (oneInThreeArities profile).flatMap noUnitArities

@[simp] theorem clauseArities_unary (first : LiteralProfile) :
    clauseArities (.unary first) =
      [.ternary, .ternary, .ternary, .ternary, .binary,
        .ternary, .binary] := by
  rfl

@[simp] theorem clauseArities_binary
    (first second : LiteralProfile) :
    clauseArities (.binary first second) =
      [.ternary, .ternary, .ternary, .ternary, .binary] := by
  rfl

@[simp] theorem clauseArities_ternary
    (first second third : LiteralProfile) :
    clauseArities (.ternary first second third) =
      [.ternary, .ternary, .ternary] := by
  rfl

/-- Exact final clause-arity stream, in source-clause order. -/
def arities (profiles : List ClauseProfile) : List Arity :=
  profiles.flatMap clauseArities

end ClauseProfileFigureNine
end PeriodicCNF
end LeanTrominoes
