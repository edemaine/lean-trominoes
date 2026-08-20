/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingCanonical
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineDirectionSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceCorrect

/-! # Exact retained Figure 9 shape from finite direction descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicOrthocrossing

/-- The specialized retained descriptor output has the canonical
clauses-then-variables layout. -/
theorem shape_isCanonical
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    FormulaShape.IsCanonical (shape source) := by
  simpa only [shape, descriptors] using
    FormulaShapeDirectionOrdering.shape_ofFormula_isCanonical
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)

/-- The finite descriptor computation produces definitionally the same
canonical logical shape as the actual clockwise, clearance-scaled Figure 9
source formula. -/
theorem shape_eq_sourceShape
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    shape source = FormulaShapeRetainedFigureNineSource.shape source := by
  simpa only [FormulaShapeRetainedFigureNineSource.shape] using
    FormulaShapeOfFormula.eq_shape_of_correct
      (retainedFigureNineClearancePositionedFormula source).erase
      (shape_isCanonical source)
      (shape_correct source sourceWidth sourceClausesNonempty)
      (FormulaShapeRetainedFigureNineSource.widthAtMostThree
        source sourceWidth)
      (FormulaShapeRetainedFigureNineSource.clausesNonempty
        source sourceClausesNonempty)

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
