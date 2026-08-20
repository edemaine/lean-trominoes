/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingFormulaSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineDirectionData
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance

/-! # Semantics of retained Figure 9 direction descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicOrthocrossing

/-- The finite descriptor stream recovers the exact clockwise-ordered
retained fixed-eight logical presentation. -/
theorem shape_correct_ordered
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    FormulaShapeOfFormula.CorrectFor
      (shape source)
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
        source).erase := by
  simpa only [shape, descriptors,
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula]
    using FormulaShapeDirectionOrdering.shape_ofFormula_correct
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_clausesNonempty
        source sourceClausesNonempty)

/-- The final whole-source clearance scale changes no logical data, so the
same finite stream is exact at the actual Figure 9 boundary. -/
theorem shape_correct
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    FormulaShapeOfFormula.CorrectFor
      (shape source)
      (retainedFigureNineClearancePositionedFormula source).erase := by
  simpa only [retainedFigureNineClearancePositionedFormula,
    PositionedPeriodicCNF.erase_scale] using
    shape_correct_ordered source sourceWidth sourceClausesNonempty

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
