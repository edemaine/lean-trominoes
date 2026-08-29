/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceTailBlocks
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordStreamSemantics

/-! # Semantic presentation of copied Figure 9 route-tail records -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineSourceTailRecord

open FormulaShapeFigureNinePolarityRouteTailRecord
open FormulaShapeFigureNineSourceTail
open FormulaShapeRetainedFigureNineDirection
open FormulaShapeRetainedFigureNineSourceTail
open PeriodicCNFStripReduction
open PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

/-- The generic copied record word is the clause-major semantic record
stream over the globally indexed final coordinated source. -/
theorem copiedRecordTokens_eq_semantic
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    copiedRecordTokens source =
      retainedFinalDirectClauseSemanticRouteTailRecordTokens source
        ((finalCoordinatedSource source).clauses.zipIdx) := by
  unfold copiedRecordTokens
    retainedFinalDirectClauseSemanticRouteTailRecordTokens
    routedCopiedClauseDescriptors copiedTailTables sourceRecordTokens
  rw [copiedOccurrenceClauses_zipIdx_eq, List.map_map]
  let clauses := (finalCoordinatedSource source).clauses.zipIdx
  change clauseRecords
      (sourceClauses
        (clauses.map fun taggedClause =>
          FormulaShapeDirectionOrdering.Token.clause
            (routedCopiedClauseProfile
              source taggedClause.2 taggedClause.1))
        (clauses.map fun taggedClause =>
          orderedTailDirections
            (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
              source)
            taggedClause.2
            (copiedOccurrenceClause
              source taggedClause.2 taggedClause.1))) =
    clauses.flatMap fun taggedClause =>
      HorizontalRoutedRouteTailRecord.clauseRecord
        (routedCopiedClauseProfile
          source taggedClause.2 taggedClause.1)
        (orderedTailDirections
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            source)
          taggedClause.2
          (copiedOccurrenceClause
            source taggedClause.2 taggedClause.1))
  induction clauses with
  | nil => rfl
  | cons taggedClause clauses induction =>
      unfold clauseRecords at induction ⊢
      simp only [List.map_cons, sourceClauses, List.headD_cons,
        List.tail_cons, List.flatMap_cons]
      rw [induction]

end FormulaShapeRetainedFigureNineSourceTailRecord
end PeriodicCNF
end LeanTrominoes
