/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFinalExactOneCorrectFor

/-! # Clause arities represented by final exact-one formula shapes -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFinalExactOne

open UnaryProgramClauseProfile

/-- Projecting literal-list lengths from an exact source shape commutes with
Figure 9, unit elimination, and polarity normalization. -/
theorem clauseLengths_eq_formula
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceShape : List FormulaShape.Token)
    (sourceCorrect : FormulaShapeOfFormula.CorrectFor sourceShape source) :
    (FormulaShape.clauseProfiles (shape sourceShape)).map
        (fun profile => profile.literals.length) =
      (PeriodicOneInThreePolarityNormalization.formula
        (PeriodicOneInThreeNoUnits.formula
          (PeriodicOneInThree.formula source))).clauses.map List.length := by
  have correct := correctFor source sourceShape sourceCorrect
  have lengths := congrArg (List.map List.length) correct.1
  simpa only [List.map_map, Function.comp_def,
    ClauseProfileOccurrenceSplit.literalProfiles,
    List.length_map] using lengths

end LeanTrominoes.PeriodicCNF.FormulaShapeFinalExactOne
