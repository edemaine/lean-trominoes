/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceCorrect
import LeanTrominoes.PeriodicCNFStripDirectRetainedFormulaShapeData

/-! # Exact semantics of direct retained formula shapes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedFormulaShapeSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedFormulaShapeSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- The direct Figure 9 source shape is exact for the actual ordered and
clearance-scaled fixed-eight formula. -/
theorem directRetainedFigureNineSourceShape_correct
    (symbols : List encoding.Γ) :
    FormulaShapeOfFormula.CorrectFor
      (directRetainedFigureNineSourceShape decider symbols)
      (retainedFigureNineClearancePositionedFormula
        (sourceFormula
          (PolySpaceCompiler.formulaOfSymbols decider symbols))).erase := by
  exact FormulaShapeRetainedFigureNineSource.correct _
    (sourceFormula_widthAtMostThree _)
    (sourceFormula_clausesNonempty _)

end PeriodicCNFStripReduction
end LeanTrominoes
