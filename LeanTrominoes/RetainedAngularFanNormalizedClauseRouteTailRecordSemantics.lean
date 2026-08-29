/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCopiedRouteTailRecordSemantics
import LeanTrominoes.RetainedAngularFanFinalCoordinatedSourceClauses

/-! # Semantic route-tail records over normalized final clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTailRecord
open PeriodicCNFStripReduction
open PeriodicOrthocrossing

/-- Semantic copied-clause records for a normalized clause sublist carrying
its original global starting index. Clause positions are canonically zero
after anchor normalization. -/
def retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (start : Nat)
    (clauses : List
      (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))) :
    List HorizontalRoutedRouteTailRecord.Token :=
  retainedFinalDirectClauseSemanticRouteTailRecordTokens formula
    ((clauses.zipIdx start).map fun taggedClause =>
      (⟨(0, 0), taggedClause.1⟩, taggedClause.2))

/-- An append of normalized clause families induces the matching semantic
record append and advances the global clause index by the first length. -/
@[simp] theorem
    retainedFinalNormalizedClauseSemanticRouteTailRecordTokens_append
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (start : Nat)
    (first second : List
      (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))) :
    retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
        formula start (first ++ second) =
      retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          formula start first ++
        retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          formula (start + first.length) second := by
  unfold retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
    retainedFinalDirectClauseSemanticRouteTailRecordTokens
  rw [List.zipIdx_append, List.map_append, List.flatMap_append]

/-- The canonical copied record word can be indexed directly over the
duplicate-free normalized final clause presentation. -/
theorem copiedRecordTokens_eq_normalizedClauseSemantic
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    copiedRecordTokens formula =
      retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
        formula 0 (deduplicatedClauses formula) := by
  rw [copiedRecordTokens_eq_semantic]
  unfold retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
    retainedFinalDirectClauseSemanticRouteTailRecordTokens
  let positionedClauses := (finalCoordinatedSource formula).clauses
  let recordBlock :
      (PositionedPeriodicClause
          (WrappedPeriodicPlanarSATVariable Variable) × Nat) →
        List HorizontalRoutedRouteTailRecord.Token := fun taggedClause =>
    HorizontalRoutedRouteTailRecord.clauseRecord
      (PeriodicCNF.FormulaShapeRetainedFigureNineDirection.routedCopiedClauseProfile
        formula taggedClause.2 taggedClause.1)
      (PeriodicCNF.FormulaShapeFigureNineSourceTail.orderedTailDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula)
        taggedClause.2
        (PeriodicCNF.FormulaShapeRetainedFigureNineDirection.copiedOccurrenceClause
          formula taggedClause.2 taggedClause.1))
  change positionedClauses.zipIdx.flatMap recordBlock = _
  calc
    positionedClauses.zipIdx.flatMap recordBlock =
        (positionedClauses.zipIdx.map fun taggedClause =>
          (⟨(0, 0), taggedClause.1.literals⟩, taggedClause.2)).flatMap
            recordBlock := by
      rw [List.flatMap_map]
      apply List.flatMap_congr
      rintro ⟨clause, clauseIndex⟩ _clauseMember
      cases clause
      rfl
    _ = (((positionedClauses.map
          PositionedPeriodicClause.literals).zipIdx).map fun taggedClause =>
            (⟨(0, 0), taggedClause.1⟩, taggedClause.2)).flatMap
              recordBlock := by
      rw [List.zipIdx_map, List.map_map]
      rfl
    _ = (((deduplicatedClauses formula).zipIdx).map fun taggedClause =>
            (⟨(0, 0), taggedClause.1⟩, taggedClause.2)).flatMap
              recordBlock := by
      rw [finalCoordinatedSource_clauseLiterals_eq]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
