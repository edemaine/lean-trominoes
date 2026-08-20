/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineDirectionData
import LeanTrominoes.PeriodicCNFStripSourceFormula

/-! # Direct retained Figure 9 direction-descriptor streams -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedDirectionDescriptorDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedDirectionDescriptorDataVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- Finite literal-profile/exit-direction descriptors for the actual guarded
PSPACE source after retained planarization and fixed-eight splitting. -/
def directRetainedFigureNineDirectionDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedFigureNineDirection.descriptors
    (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols))

end PeriodicCNFStripReduction
end LeanTrominoes
