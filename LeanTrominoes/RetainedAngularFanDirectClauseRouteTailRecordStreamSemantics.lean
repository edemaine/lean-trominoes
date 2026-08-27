/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordSemantics

/-! # Stream semantics of finite direct copied-clause records -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicCNFStripReduction
open PeriodicOrthocrossing

/-- Finite direct record queries for any presentation-ordered list of final
copied clauses carrying their original global clause indices. -/
def retainedFinalDirectClauseRouteTailRecordQueries
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedClauses : List
      (PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable) × Nat)) :
    List RetainedDirectClauseRouteTailRecordQuery :=
  taggedClauses.map fun taggedClause =>
    retainedFinalDirectClauseRouteTailRecordQuery
      formula taggedClause.2 taggedClause.1

/-- Semantic flat Figure 9 records for the same indexed copied clauses. -/
def retainedFinalDirectClauseSemanticRouteTailRecordTokens
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedClauses : List
      (PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable) × Nat)) :
    List HorizontalRoutedRouteTailRecord.Token :=
  taggedClauses.flatMap fun taggedClause =>
    HorizontalRoutedRouteTailRecord.clauseRecord
      (routedCopiedClauseProfile
        formula taggedClause.2 taggedClause.1)
      (orderedTailDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula)
        taggedClause.2
        (copiedOccurrenceClause
          formula taggedClause.2 taggedClause.1))

/-- Pointwise direct-choice correctness lifts to an exact family stream in
the original global clause order. -/
theorem retainedFinalDirectClauseRouteTailRecordStream_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ sourceClause ∈ formula.clauses, sourceClause ≠ [])
    (taggedClauses : List
      (PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable) × Nat))
    (clausesMember :
      ∀ taggedClause ∈ taggedClauses,
        taggedClause ∈ (finalCoordinatedSource formula).clauses.zipIdx)
    (clausesNonempty :
      ∀ taggedClause ∈ taggedClauses,
        taggedClause.1.literals ≠ [])
    (clausesWidth :
      ∀ taggedClause ∈ taggedClauses,
        taggedClause.1.literals.length ≤ 3)
    (choicesSome :
      ∀ taggedClause ∈ taggedClauses,
        ∀ taggedLiteral ∈ taggedClause.1.literals.zipIdx,
          ∃ choice,
            retainedFinalDirectSourceRouteChoice?
                formula taggedClause.2 taggedLiteral.2 = some choice) :
    retainedDirectClauseRouteTailRecordStream
        (retainedFinalDirectClauseRouteTailRecordQueries
          formula taggedClauses) =
      retainedFinalDirectClauseSemanticRouteTailRecordTokens
        formula taggedClauses := by
  unfold retainedDirectClauseRouteTailRecordStream
    retainedFinalDirectClauseRouteTailRecordQueries
    retainedFinalDirectClauseSemanticRouteTailRecordTokens
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  exact retainedFinalDirectClauseRouteTailRecordTokens_eq
    formula sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty
    (clausesMember taggedClause taggedClauseMember)
    (clausesNonempty taggedClause taggedClauseMember)
    (clausesWidth taggedClause taggedClauseMember)
    (choicesSome taggedClause taggedClauseMember)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
