/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorBlockData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaData

/-! # Direct retained metadata descriptor blocks -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Direct source-symbol specialization of the retained metadata clause
descriptor prefix. -/
def directRetainedPlanarMetadataClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  @FormulaShapeRetainedPlanarMetadataDirection.clauseDescriptors
    Variable directSourceVariableDecidableEq
    (directSourceFormula decider symbols)

/-- Retarget any equality with public clause descriptors to the named direct
descriptor output, without normalizing its equality implementation. -/
theorem eq_directRetainedPlanarMetadataClauseDescriptors_of_eq
    (symbols : List encoding.Γ)
    {outputDecidableEq : DecidableEq Variable}
    {tokens : List FormulaShapeDirectionOrdering.Token}
    (equal : tokens =
      @FormulaShapeRetainedPlanarMetadataDirection.clauseDescriptors
        Variable outputDecidableEq (directSourceFormula decider symbols)) :
    tokens = directRetainedPlanarMetadataClauseDescriptors decider symbols := by
  unfold directRetainedPlanarMetadataClauseDescriptors
  exact
    FormulaShapeRetainedPlanarMetadataDirection.eq_clauseDescriptors_of_decidableEq_irrel
      (directSourceFormula decider symbols) directSourceVariableDecidableEq equal

/-- Direct source-symbol specialization of the exact distinct-variable
marker suffix. -/
def directRetainedPlanarMetadataVariableMarkers
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedPlanarMetadataDirection.variableMarkers
    (sourceFormula (ProgramSource.formulaOfSymbols decider symbols))

end PeriodicCNFStripReduction
end LeanTrominoes
