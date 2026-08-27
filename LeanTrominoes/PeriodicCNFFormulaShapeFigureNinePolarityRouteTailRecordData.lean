/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteTailRecordBatchSemantics

/-! # Flat clause inputs for Figure 9 polarity route tails -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNinePolarityRouteTailRecord

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNFStripReduction
open PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord

/-- Pair every directed source clause with the next dynamic tail table.
Variable markers consume no table because they generate no Figure 9 clause. -/
def sourceClauses :
    List FormulaShapeDirectionOrdering.Token →
      List (List (List AxisDirection)) →
        List (DirectedClauseProfile × List (List AxisDirection))
  | [], _ => []
  | .variable :: source, tailTables =>
      sourceClauses source tailTables
  | .clause profile :: source, tailTables =>
      (profile, tailTables.headD []) ::
        sourceClauses source tailTables.tail

/-- Canonical finite-alphabet clause records before the bounded indexed
tail expansion. -/
def sourceRecordTokens
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    List HorizontalRoutedRouteTailRecord.Token :=
  clauseRecords (sourceClauses source tailTables)

/-- Expanding the flat clause inputs reconstructs the established aligned
header/tail record stream for the entire direction-aware formula shape. -/
@[simp] theorem batchedRecords_sourceRecordTokens
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    batchedRecords (sourceRecordTokens source tailTables) =
      FormulaShapeFigureNinePolarityRouteTail.sourceRecords
        source tailTables := by
  unfold sourceRecordTokens
  rw [batchedRecords_clauseRecords]
  induction source generalizing tailTables with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [sourceClauses,
            FormulaShapeFigureNinePolarityRouteTail.sourceRecords] using
            induction tailTables
      | clause profile =>
          simp [sourceClauses,
            FormulaShapeFigureNinePolarityRouteTail.sourceRecords,
            induction]

end FormulaShapeFigureNinePolarityRouteTailRecord
end PeriodicCNF
end LeanTrominoes
