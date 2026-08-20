/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingFormulaData
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightClauseDirectionOrdering

/-! # Finite direction descriptors at the retained Figure 9 boundary -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicOrthocrossing

/-- The finite clause-profile/exit-direction stream immediately before the
clockwise retained Figure 9 source ordering. -/
def descriptors {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeDirectionOrdering.ofFormula
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      source)

/-- Applying the fixed finite clockwise lookup to the retained descriptors. -/
def shape {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List FormulaShape.Token :=
  FormulaShapeDirectionOrdering.shape (descriptors source)

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
