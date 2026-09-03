/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalFormulaClauseAritySemantics
import LeanTrominoes.PeriodicCNFStripHorizontalRawFinalClauseAritySemantics
import LeanTrominoes.PeriodicCNFStripHorizontalTypedSourceClauseAritySemantics

/-! # Final shape arities of the horizontal typed 3DM source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

attribute [local instance] sourceVariableDecidableEq

/-- The certified final exact-one shape lists, in order, precisely the
clause arities of the typed source used by the horizontal 3DM assembly. -/
theorem retainedFinalExactOneShape_clauseLengths_eq_horizontalThreeDMTypedSourceComputed
    (source : PeriodicCNF Nat) :
    (FormulaShape.clauseProfiles
      (FormulaShapeFinalExactOne.shape
        (FormulaShapeRetainedFigureNineSource.shape
          (sourceFormula source)))).map
          (fun profile => profile.literals.length) =
      (horizontalThreeDMTypedSourceComputed source).clauses.map
        List.length := by
  calc
    _ =
        (PeriodicOneInThreePolarityNormalization.formula
          (PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            (sourceFormula source)).erase).clauses.map List.length :=
      retainedFinalExactOneShape_clauseLengths_eq_raw
        (sourceFormula source)
        (sourceFormula_widthAtMostThree source)
        (sourceFormula_clausesNonempty source)
    _ =
        (PeriodicOneInThreePolarityNormalization.formula
          (horizontalFormula source).erase).clauses.map List.length :=
      (horizontalFormula_polarityClauseLengths_eq_raw source).symm
    _ = _ :=
      (horizontalThreeDMTypedSourceComputed_clauseLengths_eq_horizontalFormula
        source).symm

end LeanTrominoes.PeriodicCNFStripReduction
