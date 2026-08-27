/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailRecordData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceTailData

/-! # Flat retained Figure 9 source-tail clause records -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineSourceTailRecord

open PeriodicCNFStripReduction
open PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord

/-- Canonical finite-alphabet clause input for the retained fixed-eight
Figure 9 route source. -/
def recordTokens {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List HorizontalRoutedRouteTailRecord.Token :=
  FormulaShapeFigureNinePolarityRouteTailRecord.sourceRecordTokens
    (FormulaShapeRetainedFigureNineDirection.descriptors source)
    (FormulaShapeRetainedFigureNineSourceTail.tailTables source)

/-- The bounded clause expander maps the retained flat input to the exact
established retained header/tail records. -/
@[simp] theorem batchedRecords_recordTokens
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    batchedRecords (recordTokens source) =
      FormulaShapeRetainedFigureNineSourceTail.records source := by
  unfold recordTokens FormulaShapeRetainedFigureNineSourceTail.records
  exact
    FormulaShapeFigureNinePolarityRouteTailRecord.batchedRecords_sourceRecordTokens
      (FormulaShapeRetainedFigureNineDirection.descriptors source)
      (FormulaShapeRetainedFigureNineSourceTail.tailTables source)

end FormulaShapeRetainedFigureNineSourceTailRecord
end PeriodicCNF
end LeanTrominoes
