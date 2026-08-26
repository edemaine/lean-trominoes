/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedSourceDirectionQuery
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCopiedDirectionData

/-! # Finite clause queries for final copied descriptors -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

/-- The copied-direction namespace wrapper is definitionally the public
final copied-source lookup. -/
private theorem retainedFinalCopiedSourceFirstDirection_eq_copiedFirstDirection
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)) :
    retainedFinalCopiedSourceFirstDirection
        formula clauseIndex literalIndex literal =
      FormulaShapeRetainedFigureNineDirection.copiedFirstDirection
        formula clauseIndex literalIndex literal := by
  rfl

/-- A width-three copied clause whose directions remain as finite mixed
direct/fallback queries. -/
inductive RetainedFinalCopiedClauseQuery
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

/-- Total width-three packing of literal profiles with unevaluated direction
queries. -/
def RetainedFinalCopiedClauseQuery.ofList :
    List (LiteralProfile × RetainedFinalCopiedSourceDirectionQuery) →
      RetainedFinalCopiedClauseQuery
  | [] => default
  | [(first, firstDirection)] =>
      .unary first firstDirection
  | [(first, firstDirection), (second, secondDirection)] =>
      .binary first firstDirection second secondDirection
  | (first, firstDirection) :: (second, secondDirection) ::
      (third, thirdDirection) :: _ =>
      .ternary first firstDirection second secondDirection
        third thirdDirection

/-- Evaluate a finite copied-clause query to one direction-aware descriptor
token. -/
def retainedFinalCopiedClauseDescriptorOfQuery :
    RetainedFinalCopiedClauseQuery →
      FormulaShapeDirectionOrdering.Token
  | .unary first firstDirection =>
      .clause (.unary first
        (retainedFinalCopiedSourceDirectionOfQuery firstDirection))
  | .binary first firstDirection second secondDirection =>
      .clause (.binary first
        (retainedFinalCopiedSourceDirectionOfQuery firstDirection)
        second
        (retainedFinalCopiedSourceDirectionOfQuery secondDirection))
  | .ternary first firstDirection second secondDirection
      third thirdDirection =>
      .clause (.ternary first
        (retainedFinalCopiedSourceDirectionOfQuery firstDirection)
        second
        (retainedFinalCopiedSourceDirectionOfQuery secondDirection)
        third
        (retainedFinalCopiedSourceDirectionOfQuery thirdDirection))

/-- Evaluation commutes with total width-three list packing. -/
theorem retainedFinalCopiedClauseDescriptorOfQuery_ofList
    (items :
      List (LiteralProfile × RetainedFinalCopiedSourceDirectionQuery)) :
    retainedFinalCopiedClauseDescriptorOfQuery
        (RetainedFinalCopiedClauseQuery.ofList items) =
      .clause
        (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
          (items.map fun item =>
            (item.1,
              retainedFinalCopiedSourceDirectionOfQuery item.2))) := by
  cases items with
  | nil => rfl
  | cons first rest =>
    cases rest with
    | nil => rfl
    | cons second rest =>
      cases rest with
      | nil => rfl
      | cons third rest => rfl

/-- Exact finite clause query associated with one final copied clause. -/
def retainedFinalCopiedClauseQuery
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PositionedPeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :
    RetainedFinalCopiedClauseQuery :=
  RetainedFinalCopiedClauseQuery.ofList
    (clause.literals.zipIdx.map fun taggedLiteral =>
      (FormulaShapeDirectionOrdering.literalProfile taggedLiteral.1,
        retainedFinalCopiedSourceDirectionQuery
          formula clauseIndex taggedLiteral.2 taggedLiteral.1))

/-- Evaluating a finite clause query is exactly the public copied-clause
descriptor. -/
theorem retainedFinalCopiedClauseDescriptorOfQuery_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PositionedPeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :
    retainedFinalCopiedClauseDescriptorOfQuery
        (retainedFinalCopiedClauseQuery formula clauseIndex clause) =
      .clause
        (FormulaShapeRetainedFigureNineDirection.copiedClauseProfile
          formula clauseIndex clause) := by
  unfold retainedFinalCopiedClauseQuery
  rw [retainedFinalCopiedClauseDescriptorOfQuery_ofList]
  apply congrArg FormulaShapeDirectionOrdering.Token.clause
  apply congrArg
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
  rw [List.map_map]
  apply List.map_congr_left
  intro taggedLiteral _
  simpa only [Function.comp_apply] using
    congrArg
      (fun direction =>
        (FormulaShapeDirectionOrdering.literalProfile taggedLiteral.1,
          direction))
      ((retainedFinalCopiedSourceDirectionOfQuery_eq
          formula clauseIndex taggedLiteral.2 taggedLiteral.1).trans
        (retainedFinalCopiedSourceFirstDirection_eq_copiedFirstDirection
          formula clauseIndex taggedLiteral.2 taggedLiteral.1))

/-- Presentation-ordered finite query stream for all final copied clauses. -/
def retainedFinalCopiedClauseQueries
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List RetainedFinalCopiedClauseQuery :=
  (finalCoordinatedSource formula).clauses.zipIdx.map fun taggedClause =>
    retainedFinalCopiedClauseQuery
      formula taggedClause.2 taggedClause.1

/-- Evaluate a finite clause-query stream to descriptor tokens. -/
def retainedFinalCopiedClauseDescriptors
    (queries : List RetainedFinalCopiedClauseQuery) :
    List FormulaShapeDirectionOrdering.Token :=
  queries.flatMap fun query =>
    [retainedFinalCopiedClauseDescriptorOfQuery query]

/-- Evaluating the semantic query stream gives exactly the finite copied
descriptor prefix. -/
theorem retainedFinalCopiedClauseDescriptors_queries_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    retainedFinalCopiedClauseDescriptors
        (retainedFinalCopiedClauseQueries formula) =
      FormulaShapeRetainedFigureNineDirection.copiedClauseDescriptors
        formula := by
  unfold retainedFinalCopiedClauseDescriptors
    retainedFinalCopiedClauseQueries
    FormulaShapeRetainedFigureNineDirection.copiedClauseDescriptors
  induction (finalCoordinatedSource formula).clauses.zipIdx with
  | nil => rfl
  | cons taggedClause taggedClauses induction =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [retainedFinalCopiedClauseDescriptorOfQuery_eq, induction]
      simp only [List.singleton_append]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
