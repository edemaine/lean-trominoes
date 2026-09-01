/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteTailRecordBatchSemantics
import LeanTrominoes.RetainedAngularFanNormalizedClauseRouteTailRecordSemantics

/-! # Batched semantics of normalized final clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicCNFStripReduction
open PeriodicOrthocrossing

/-- Batching a normalized semantic clause stream expands each canonical
input clause record to its complete routed header/tail records. -/
theorem batchedRecords_retainedFinalNormalizedClauseSemantic
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (start : Nat)
    (clauses : List
      (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))) :
    HorizontalRoutedRouteTailRecord.batchedRecords
        (retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          formula start clauses) =
      ((clauses.zipIdx start).map fun taggedClause =>
          (⟨(0, 0), taggedClause.1⟩, taggedClause.2)).flatMap
        fun taggedClause =>
          sourceClauseRecords
            (routedCopiedClauseProfile
              formula taggedClause.2 taggedClause.1)
            (orderedTailDirections
              (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
                formula)
              taggedClause.2
              (copiedOccurrenceClause
                formula taggedClause.2 taggedClause.1)) := by
  let taggedClauses : List
      (PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable) × Nat) :=
    (clauses.zipIdx start).map fun taggedClause =>
      (⟨(0, 0), taggedClause.1⟩, taggedClause.2)
  let clauseData := taggedClauses.map fun taggedClause =>
    (routedCopiedClauseProfile formula taggedClause.2 taggedClause.1,
      orderedTailDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula)
        taggedClause.2
        (copiedOccurrenceClause formula taggedClause.2 taggedClause.1))
  have inputEq :
      retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          formula start clauses =
        HorizontalRoutedRouteTailRecord.clauseRecords clauseData := by
    unfold retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
      retainedFinalDirectClauseSemanticRouteTailRecordTokens
      HorizontalRoutedRouteTailRecord.clauseRecords clauseData taggedClauses
    simp only [List.map_map, List.flatMap_map, Function.comp_apply]
  rw [inputEq, HorizontalRoutedRouteTailRecord.batchedRecords_clauseRecords]
  unfold clauseData taggedClauses
  rw [List.flatMap_map]

/-- A normalized semantic clause-family stream is a complete batching prefix,
so it can be expanded independently of every following record family. -/
@[simp] theorem
    batchedRecords_retainedFinalNormalizedClauseSemantic_append
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (start : Nat)
    (clauses : List
      (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)))
    (rest : List HorizontalRoutedRouteTailRecord.Token) :
    HorizontalRoutedRouteTailRecord.batchedRecords
        (retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          formula start clauses ++ rest) =
      HorizontalRoutedRouteTailRecord.batchedRecords
          (retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
            formula start clauses) ++
        HorizontalRoutedRouteTailRecord.batchedRecords rest := by
  let taggedClauses : List
      (PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable) × Nat) :=
    (clauses.zipIdx start).map fun taggedClause =>
      (⟨(0, 0), taggedClause.1⟩, taggedClause.2)
  let clauseData := taggedClauses.map fun taggedClause =>
    (routedCopiedClauseProfile formula taggedClause.2 taggedClause.1,
      orderedTailDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula)
        taggedClause.2
        (copiedOccurrenceClause formula taggedClause.2 taggedClause.1))
  have inputEq :
      retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          formula start clauses =
        HorizontalRoutedRouteTailRecord.clauseRecords clauseData := by
    unfold retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
      retainedFinalDirectClauseSemanticRouteTailRecordTokens
      HorizontalRoutedRouteTailRecord.clauseRecords clauseData taggedClauses
    simp only [List.map_map, List.flatMap_map, Function.comp_apply]
  rw [inputEq,
    HorizontalRoutedRouteTailRecord.batchedRecords_clauseRecords_append]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
