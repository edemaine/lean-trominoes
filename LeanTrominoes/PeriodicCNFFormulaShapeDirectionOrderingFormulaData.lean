/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineEndpointDirectionData
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingData

/-! # Canonical direction descriptors of positioned formulas -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeDirectionOrdering

open ClauseProfileOccurrenceSplit
open UnaryProgramClauseProfile

/-- Route-relevant finite data of one arbitrary typed periodic literal. -/
def literalProfile {Variable : Type}
    (literal : PeriodicLiteral Variable) : LiteralProfile :=
  { nextSlice := decide (literal.offset = ((1, 0) : Cell))
    value := literal.value }

@[simp] theorem map_literalProfile {Variable : Type}
    (clause : PeriodicClause Variable) :
    clause.map literalProfile = literalProfiles clause :=
  rfl

/-- Total packing of a list of annotated literals into the finite
width-three descriptor alphabet. -/
def DirectedClauseProfile.ofList :
    List (LiteralProfile × AxisDirection) → DirectedClauseProfile
  | [] => default
  | [(first, firstDirection)] =>
      .unary first firstDirection
  | [(first, firstDirection), (second, secondDirection)] =>
      .binary first firstDirection second secondDirection
  | (first, firstDirection) :: (second, secondDirection) ::
      (third, thirdDirection) :: _ =>
      .ternary first firstDirection second secondDirection
        third thirdDirection

/-- Annotate each original literal with its finite semantic profile and the
first direction of its corresponding incidence route. -/
def annotatedLiterals {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable) :
    List (LiteralProfile × AxisDirection) :=
  clause.literals.zipIdx.map fun taggedLiteral =>
    (literalProfile taggedLiteral.1,
      AxisDirection.polylineFirstDirection
        (routes clauseIndex taggedLiteral.2))

/-- Canonical finite direction descriptor of one positioned clause. -/
def DirectedClauseProfile.ofClause {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable) :
    DirectedClauseProfile :=
  .ofList (annotatedLiterals routes clauseIndex clause)

/-- Canonical annotated formula shape before the finite clockwise lookup:
one descriptor per clause, followed by one marker per distinct variable. -/
def ofFormula {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : List Token :=
  (source.clauses.zipIdx.map fun taggedClause =>
      .clause (.ofClause routes taggedClause.2 taggedClause.1)) ++
    List.replicate source.erase.variableOccurrences.dedup.length .variable

end FormulaShapeDirectionOrdering
end PeriodicCNF
end LeanTrominoes
