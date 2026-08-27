/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineDirectionData

/-! # Retained Figure 9 source-tail tables and records -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineSourceTail

open PeriodicOrthocrossing

/-- One clockwise dynamic-tail table per retained fixed-eight source clause,
in the same clause order as the finite direction descriptors. -/
def tailTables {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (List (List AxisDirection)) :=
  let positioned :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source
  let routes :=
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      source
  positioned.clauses.zipIdx.map fun taggedClause =>
    FormulaShapeFigureNineSourceTail.orderedTailDirections
      routes taggedClause.2 taggedClause.1

/-- The retained tail table has exactly one row per source clause. -/
@[simp] theorem tailTables_length
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (tailTables source).length =
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source).clauses.length := by
  simp [tailTables]

/-- Exact delimited header/tail records at the retained Figure 9 boundary. -/
def records {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List
      PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderTail.Token :=
  FormulaShapeFigureNinePolarityRouteTail.sourceRecords
    (FormulaShapeRetainedFigureNineDirection.descriptors source)
    (tailTables source)

end FormulaShapeRetainedFigureNineSourceTail
end PeriodicCNF
end LeanTrominoes
