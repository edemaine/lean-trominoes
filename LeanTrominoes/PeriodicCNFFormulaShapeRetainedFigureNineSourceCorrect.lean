/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceNonempty
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceWidth

/-! # Certified exact shapes at the retained Figure 9 boundary -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineSource

open PeriodicOrthocrossing

/-- The actual clockwise, clearance-scaled fixed-eight source has the exact
canonical shape consumed by Figure 9. -/
theorem correct
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    FormulaShapeOfFormula.CorrectFor
      (shape source)
      (retainedFigureNineClearancePositionedFormula source).erase := by
  exact shape_correct source
    (widthAtMostThree source sourceWidth)
    (clausesNonempty source sourceClausesNonempty)

end FormulaShapeRetainedFigureNineSource
end PeriodicCNF
end LeanTrominoes
