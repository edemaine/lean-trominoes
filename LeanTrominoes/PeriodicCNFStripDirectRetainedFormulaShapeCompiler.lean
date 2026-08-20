/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFinalExactOneCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedFormulaShapeData
import LeanTrominoes.TM2CompositionMachine

/-! # Conditional direct retained formula-shape compilation -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedFormulaShapeCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The sole formula-shape machine still required before the already compiled
fixed finite exact-one postprocessing can run. -/
abbrev DirectRetainedFigureNineSourceShapeCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShape.Token)
    encoding.Γ FormulaShape.Token id id
    (directRetainedFigureNineSourceShape decider)

/-- Once the actual ordered retained source shape is available, the complete
final exact-one shape follows by a fixed finite block transduction. -/
noncomputable def directRetainedFinalExactOneShapeComputableInPolyTime
    (sourceShape : DirectRetainedFigureNineSourceShapeCompiler decider) :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List FormulaShape.Token)
      encoding.Γ FormulaShape.Token id id
      (directRetainedFinalExactOneShape decider) := by
  let complete := TM2CompositionMachine.computableInPolyTime sourceShape
    FormulaShapeFinalExactOne.shapeComputableInPolyTime
  unfold directRetainedFinalExactOneShape
  exact complete

end PeriodicCNFStripReduction
end LeanTrominoes
