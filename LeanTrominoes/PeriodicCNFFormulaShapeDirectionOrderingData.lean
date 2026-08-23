/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AxisDirectionClockwiseRankData
import LeanTrominoes.PeriodicCNFFormulaShapeOfFormulaData
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingTokenData

/-! # Finite direction-aware formula-shape ordering -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeDirectionOrdering

open UnaryProgramClauseProfile

/-- Literal profiles paired with route directions in the incoming clause
order. -/
def DirectedClauseProfile.taggedLiterals :
    DirectedClauseProfile → List (LiteralProfile × AxisDirection)
  | .unary first firstDirection =>
      [(first, firstDirection)]
  | .binary first firstDirection second secondDirection =>
      [(first, firstDirection), (second, secondDirection)]
  | .ternary first firstDirection second secondDirection third thirdDirection =>
      [(first, firstDirection), (second, secondDirection),
        (third, thirdDirection)]

/-- Stable clockwise comparison on finite route directions. -/
def directionLE
    (first second : LiteralProfile × AxisDirection) : Prop :=
  first.2.clockwiseRank ≤ second.2.clockwiseRank

instance : DecidableRel directionLE := by
  intro first second
  unfold directionLE
  infer_instance

/-- Stable clockwise ordering of one direction-annotated clause profile. -/
def DirectedClauseProfile.orderedLiterals
    (profile : DirectedClauseProfile) : List LiteralProfile :=
  (profile.taggedLiterals.insertionSort directionLE).map Prod.fst

/-- Repackage the nonempty width-three sorted literal list.  The total
fallback branches in `clauseProfile` are unreachable for these constructors. -/
def DirectedClauseProfile.orderedProfile
    (profile : DirectedClauseProfile) : ClauseProfile :=
  FormulaShapeOfFormula.clauseProfile profile.orderedLiterals

/-- Forget route directions after applying the stable clockwise sort. -/
def tokenBlock : Token → List FormulaShape.Token
  | .clause profile => [.clause profile.orderedProfile]
  | .variable => [.variable]

/-- Complete ordinary formula shape obtained by sorting every annotated
clause and retaining every distinct-variable marker. -/
def shape (source : List Token) : List FormulaShape.Token :=
  source.flatMap tokenBlock

@[simp] theorem variableMarkers_tokenBlock (token : Token) :
    FormulaShape.variableMarkers (tokenBlock token) =
      match token with
      | .clause _ => []
      | .variable => [()] := by
  cases token <;> rfl

@[simp] theorem shape_nil : shape [] = [] :=
  rfl

@[simp] theorem shape_cons (token : Token) (source : List Token) :
    shape (token :: source) = tokenBlock token ++ shape source :=
  rfl

@[simp] theorem variableCount_shape (source : List Token) :
    FormulaShape.variableCount (shape source) =
      (source.filterMap fun
        | .clause _ => none
        | .variable => some ()).length := by
  unfold shape FormulaShape.variableCount
  induction source with
  | nil => rfl
  | cons token source induction =>
      rw [List.flatMap_cons, FormulaShape.variableMarkers_append,
        variableMarkers_tokenBlock]
      cases token <;> simp [induction]

end FormulaShapeDirectionOrdering
end PeriodicCNF
end LeanTrominoes
