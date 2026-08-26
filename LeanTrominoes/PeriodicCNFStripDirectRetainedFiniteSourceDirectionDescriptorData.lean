/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineFiniteDirectionFixedEight
import LeanTrominoes.PeriodicCNFStripSourceFormula

/-! # Direct finite copied-source descriptor blocks -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedFiniteSourceDirectionDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedFiniteSourceDirectionDataVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- Copied-clause lookup prefix specialized to direct source symbols. -/
def directRetainedFigureNineCopiedClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedFigureNineDirection.copiedClauseDescriptors
    (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols))

/-- One marker per stable retained source variable, before fixed-eight
expansion. -/
def directRetainedFigureNineFiniteSourceVariableMarkers
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  let source :=
    sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols)
  List.replicate
    (PeriodicThreeSATThree.sourceVariables
      (FormulaShapeRetainedFigureNineDirection.sourceScaledForFigureSeven
        source).erase).length
    .variable

/-- Direct source-symbol specialization of the copied lookup prefix followed
by one marker per stable retained source variable. -/
def directRetainedFigureNineFiniteSourceDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedFigureNineDirection.finiteSourceDescriptors
    (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols))

/-- The finite-source target is exactly its separately streamable copied
clause and variable-marker phases. -/
theorem directRetainedFigureNineFiniteSourceDescriptors_eq_blocks
    (symbols : List encoding.Γ) :
    directRetainedFigureNineFiniteSourceDescriptors decider symbols =
      directRetainedFigureNineCopiedClauseDescriptors decider symbols ++
        directRetainedFigureNineFiniteSourceVariableMarkers
          decider symbols := by
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes
