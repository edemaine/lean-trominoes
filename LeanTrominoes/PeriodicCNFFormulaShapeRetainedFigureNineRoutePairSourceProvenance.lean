/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRoutePairSourceProvenance
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineDirectionData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceTailData

/-! # Retained source-clause provenance of Figure 9 route pairs -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeFigureNineSourceTail
open PeriodicOrthocrossing

/-- A retained Figure 9 pair remembers the exact refined source clause that
created its header and supplied its clockwise dynamic tail table. -/
theorem exists_sourceClause_of_mem_sourcePairs
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (pair : FormulaShapeFigureNinePolarityRouteHeader.Header ×
      List AxisDirection)
    (pairMember : pair ∈
      FormulaShapeFigureNinePolarityRouteTail.sourcePairs
        (FormulaShapeRetainedFigureNineDirection.descriptors source)
        (tailTables source)) :
    ∃ clause clauseIndex,
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx ∧
      pair.1 ∈ sourceClauseHeaders
        (DirectedClauseProfile.ofClause
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            source)
          clauseIndex clause) ∧
      pair.2 =
        selectedTailDirections
          (orderedTailDirections
            (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
              source)
            clauseIndex clause)
          pair.1 := by
  exact
    FormulaShapeFigureNinePolarityRouteTail.exists_sourceClause_of_mem_sourcePairs_ofFormula
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
      pair
      (by simpa only [FormulaShapeRetainedFigureNineDirection.descriptors,
        tailTables] using pairMember)

end FormulaShapeRetainedFigureNineSourceTail
end PeriodicCNF
end LeanTrominoes
