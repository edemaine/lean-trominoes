/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalFinalClauseAritySemantics

/-! # Raw positioned realization of the final clause arities -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicOrthocrossing

/-- The certified final shape arities are those of polarity normalization
applied to the raw ordered Figure 9 and unit-elimination endpoint. -/
theorem retainedFinalExactOneShape_clauseLengths_eq_raw
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    (FormulaShape.clauseProfiles
      (FormulaShapeFinalExactOne.shape
        (FormulaShapeRetainedFigureNineSource.shape source))).map
          (fun profile => profile.literals.length) =
      (PeriodicOneInThreePolarityNormalization.formula
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase).clauses.map List.length := by
  rw [retainedFinalExactOneShape_clauseLengths
    source sourceWidth sourceClausesNonempty]
  rw [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase]

end LeanTrominoes.PeriodicCNFStripReduction

