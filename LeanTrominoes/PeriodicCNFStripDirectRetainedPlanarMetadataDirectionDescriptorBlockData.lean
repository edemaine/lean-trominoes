/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorBlockData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorData

/-! # Direct retained metadata descriptor blocks -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedMetadataBlockDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedMetadataBlockDataVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- Direct source-symbol specialization of the retained metadata clause
descriptor prefix. -/
def directRetainedPlanarMetadataClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedPlanarMetadataDirection.clauseDescriptors
    (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols))

/-- Direct source-symbol specialization of the exact distinct-variable
marker suffix. -/
def directRetainedPlanarMetadataVariableMarkers
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedPlanarMetadataDirection.variableMarkers
    (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols))

end PeriodicCNFStripReduction
end LeanTrominoes
