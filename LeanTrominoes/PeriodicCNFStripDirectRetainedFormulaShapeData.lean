/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFinalExactOneData
import LeanTrominoes.PeriodicCNFStripSourceFormula

/-! # Direct retained formula-shape data for strip hardness -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedFormulaShapeDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedFormulaShapeDataVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- Exact clockwise, clearance-scaled fixed-eight shape that is consumed by
Figure 9 for a generated PSPACE-source word. -/
def directRetainedFigureNineSourceShape (symbols : List encoding.Γ) :
    List FormulaShape.Token :=
  FormulaShapeRetainedFigureNineSource.shape
    (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols))

/-- Exact final logical shape after Figure 9, unit-clause removal, and
polarity normalization. -/
def directRetainedFinalExactOneShape (symbols : List encoding.Γ) :
    List FormulaShape.Token :=
  FormulaShapeFinalExactOne.shape
    (directRetainedFigureNineSourceShape decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

