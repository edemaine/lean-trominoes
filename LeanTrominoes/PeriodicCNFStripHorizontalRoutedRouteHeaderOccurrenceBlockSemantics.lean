/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailRecordData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceBlockCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceCompiler

/-! # Semantics of parent-clause occurrence blocks -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderOccurrenceBlock

open PeriodicCNF
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTailRecord

/-- Projecting a completed source-clause record forgets its dynamic tails and
returns exactly the finite occurrence block determined by its header. -/
@[simp] theorem occurrenceOutput_sourceClauseRecords
    (profile : DirectedClauseProfile)
    (orderedTails : List (List AxisDirection)) :
    HorizontalRoutedRouteHeaderOccurrence.output
        (sourceClauseRecords profile orderedTails) =
      tokenBlock (.clause profile) := by
  simp [sourceClauseRecords, sourceClausePairs, tokenBlock]

/-- The header projection of a complete source record stream is independent
of its aligned dynamic tail tables. -/
theorem occurrenceOutput_sourceRecords
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    HorizontalRoutedRouteHeaderOccurrence.output
        (FormulaShapeFigureNinePolarityRouteTail.sourceRecords
          source tailTables) =
      output source := by
  induction source generalizing tailTables with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [FormulaShapeFigureNinePolarityRouteTail.sourceRecords,
            output, tokenBlock] using induction tailTables
      | clause profile =>
          simp [FormulaShapeFigureNinePolarityRouteTail.sourceRecords,
            output, tokenBlock, induction]

/-- Equivalently, batch-expanding the flat record tokens before projecting
their headers yields the descriptor-wise occurrence expansion. -/
theorem occurrenceOutput_batchedRecords_sourceRecordTokens
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    HorizontalRoutedRouteHeaderOccurrence.output
        (HorizontalRoutedRouteTailRecord.batchedRecords
          (sourceRecordTokens source tailTables)) =
      output source := by
  rw [batchedRecords_sourceRecordTokens]
  exact occurrenceOutput_sourceRecords source tailTables

end HorizontalRoutedRouteHeaderOccurrenceBlock
end PeriodicCNFStripReduction
end LeanTrominoes
