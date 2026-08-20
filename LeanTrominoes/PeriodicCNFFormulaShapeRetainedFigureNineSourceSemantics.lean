/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeOfFormulaSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceData

/-! # Exact semantics at the retained Figure 9 source boundary -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineSource

open PeriodicOrthocrossing

/-- The canonical boundary shape gives the exact ordered profiles and exact
distinct-variable count consumed by the Figure 9 transformation. -/
theorem shape_correct
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (width :
      (retainedFigureNineClearancePositionedFormula
        source).erase.WidthAtMost 3)
    (nonempty :
      ∀ clause ∈
          (retainedFigureNineClearancePositionedFormula source).erase.clauses,
        clause ≠ []) :
    FormulaShapeOfFormula.CorrectFor
      (shape source)
      (retainedFigureNineClearancePositionedFormula source).erase := by
  exact FormulaShapeOfFormula.shape_correct _ width nonempty

end FormulaShapeRetainedFigureNineSource
end PeriodicCNF
end LeanTrominoes
