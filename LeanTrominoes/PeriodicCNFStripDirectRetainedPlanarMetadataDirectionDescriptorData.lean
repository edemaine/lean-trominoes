/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorData
import LeanTrominoes.PeriodicCNFStripSourceFormula

/-! # Direct retained planar metadata descriptors -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedPlanarMetadataDirectionDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedPlanarMetadataDirectionDataVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- Position-free retained direction descriptors generated from a direct
PSPACE source-symbol word through the explicit finite metadata boundary. -/
def directRetainedPlanarMetadataDirectionDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedPlanarMetadataDirection.descriptors
    (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols))

end PeriodicCNFStripReduction
end LeanTrominoes
