/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineFiniteDirectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedDirectionDescriptorData

/-! # Direct finite retained Figure 9 direction descriptors -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedFiniteDirectionDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedFiniteDirectionDataVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- Proof-free finite copied/cycle lookup stream specialized to the guarded
direct source word. -/
def directRetainedFigureNineFiniteDirectionDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedFigureNineDirection.finiteDescriptors
    (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols))

/-- The actual normalized direct Figure 9 route descriptors are exactly the
specialized finite lookup stream. -/
theorem directRetainedFigureNineDirectionDescriptors_eq_finite
    (symbols : List encoding.Γ) :
    directRetainedFigureNineDirectionDescriptors decider symbols =
      directRetainedFigureNineFiniteDirectionDescriptors decider symbols := by
  unfold directRetainedFigureNineDirectionDescriptors
    directRetainedFigureNineFiniteDirectionDescriptors
  exact FormulaShapeRetainedFigureNineDirection.descriptors_eq_finiteDescriptors
    (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols))
    (sourceFormula_isLocal _)
    (sourceFormula_widthAtMostThree _)
    (sourceFormula_occurrencesAtMostThree _)
    (sourceFormula_clausesNonempty _)

end PeriodicCNFStripReduction
end LeanTrominoes
