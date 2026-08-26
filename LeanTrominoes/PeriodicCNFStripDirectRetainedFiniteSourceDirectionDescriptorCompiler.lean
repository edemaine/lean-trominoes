/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightDirectionGeneratedCompiler
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineFiniteDirectionFixedEight
import LeanTrominoes.PeriodicCNFStripDirectRetainedDirectionDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedFiniteDirectionDescriptorData

/-! # Direct compiler boundary for finite copied-source descriptors -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedFiniteSourceDirectionCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedFiniteSourceDirectionCompilerVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- Direct source-symbol specialization of the copied lookup prefix followed
by one marker per stable retained source variable. -/
def directRetainedFigureNineFiniteSourceDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedFigureNineDirection.finiteSourceDescriptors
    (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols))

/-- The sole remaining finite direction boundary after reusing the existing
fixed-eight cycle and marker phases. -/
abbrev DirectRetainedFigureNineFiniteSourceDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token
    id id (directRetainedFigureNineFiniteSourceDescriptors decider)

/-- Any compiler for the finite copied-source stream composes with the
existing fixed-eight expander to compile the actual final normalized route
descriptor stream. -/
noncomputable def directRetainedFigureNineDirectionDescriptorCompilerOfFiniteSource
    (sourceCompiler :
      DirectRetainedFigureNineFiniteSourceDescriptorCompiler decider) :
    DirectRetainedFigureNineDirectionDescriptorCompiler decider := by
  let expanded :=
    FormulaShapeFixedEightDirection.descriptorsComputableInPolyTimeOf
      id (directRetainedFigureNineFiniteSourceDescriptors decider)
      sourceCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    expanded fun symbols => by
      unfold directRetainedFigureNineFiniteSourceDescriptors
      rw [FormulaShapeRetainedFigureNineDirection.fixedEightDescriptors_finiteSourceDescriptors_eq_finiteDescriptors]
      exact
        (directRetainedFigureNineDirectionDescriptors_eq_finite
          decider symbols).symm

end PeriodicCNFStripReduction
end LeanTrominoes
