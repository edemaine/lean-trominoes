/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFinalExactOneClauseAritySemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceCorrect

/-! # Semantic clause arities of the horizontal exact-one endpoint -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicOrthocrossing

/-- The certified retained final shape enumerates exactly the clause arities
of the three ordinary logical exact-one transformations. -/
theorem retainedFinalExactOneShape_clauseLengths
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    (FormulaShape.clauseProfiles
      (FormulaShapeFinalExactOne.shape
        (FormulaShapeRetainedFigureNineSource.shape source))).map
          (fun profile => profile.literals.length) =
      (PeriodicOneInThreePolarityNormalization.formula
        (PeriodicOneInThreeNoUnits.formula
          (PeriodicOneInThree.formula
            (retainedFigureNineClearancePositionedFormula
              source).erase))).clauses.map List.length := by
  exact FormulaShapeFinalExactOne.clauseLengths_eq_formula
    (retainedFigureNineClearancePositionedFormula source).erase
    (FormulaShapeRetainedFigureNineSource.shape source)
    (FormulaShapeRetainedFigureNineSource.correct
      source sourceWidth sourceClausesNonempty)

end LeanTrominoes.PeriodicCNFStripReduction
