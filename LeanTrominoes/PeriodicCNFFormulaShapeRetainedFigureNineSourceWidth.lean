/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceData

/-! # Width at the retained Figure 9 source boundary -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineSource

open PeriodicOrthocrossing

theorem widthAtMostThree
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3) :
    (retainedFigureNineClearancePositionedFormula
      source).erase.WidthAtMost 3 :=
  retainedFigureNineClearancePositionedFormula_widthAtMostThree
    source sourceWidth

end FormulaShapeRetainedFigureNineSource
end PeriodicCNF
end LeanTrominoes
