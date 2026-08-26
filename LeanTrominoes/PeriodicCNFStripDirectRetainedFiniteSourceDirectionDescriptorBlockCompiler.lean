/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFiniteSourceDirectionDescriptorCompiler
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Two-pass direct finite copied-source descriptor compilation -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedFiniteSourceDirectionBlockCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- First retained-input pass: append the finite normalized direct/fallback
descriptor of every copied retained clause. -/
abbrev DirectRetainedFigureNineCopiedClauseDescriptorAppender :=
  TM2ComputableInPolyTime id id
    (RetainedInputAppendPipeline.appended
      (directRetainedFigureNineCopiedClauseDescriptors decider))

/-- Second retained-input pass: recover the source symbols and append one
marker per stable retained source variable. -/
abbrev DirectRetainedFigureNineFiniteSourceVariableMarkerAppender :=
  TM2ComputableInPolyTime id id
    (RetainedInputAppendPipeline.appendFromWorkspace
      (directRetainedFigureNineFiniteSourceVariableMarkers decider))

/-- The two independently streamable passes compile the finite copied-source
input expected by the existing fixed-eight expander. -/
noncomputable def directRetainedFigureNineFiniteSourceDescriptorCompilerOfAppenders
    (clauses :
      DirectRetainedFigureNineCopiedClauseDescriptorAppender decider)
    (markers :
      DirectRetainedFigureNineFiniteSourceVariableMarkerAppender decider) :
    DirectRetainedFigureNineFiniteSourceDescriptorCompiler decider := by
  exact RetainedInputAppendPipeline.computableInPolyTimeOfAppendersEq
    (directRetainedFigureNineCopiedClauseDescriptors decider)
    (directRetainedFigureNineFiniteSourceVariableMarkers decider)
    (directRetainedFigureNineFiniteSourceDescriptors decider)
    (fun symbols =>
      (directRetainedFigureNineFiniteSourceDescriptors_eq_blocks
        decider symbols).symm)
    clauses markers

/-- Consequently the two source passes compile the actual final normalized
Figure 9 route-descriptor stream. -/
noncomputable def directRetainedFigureNineDirectionDescriptorCompilerOfAppenders
    (clauses :
      DirectRetainedFigureNineCopiedClauseDescriptorAppender decider)
    (markers :
      DirectRetainedFigureNineFiniteSourceVariableMarkerAppender decider) :
    DirectRetainedFigureNineDirectionDescriptorCompiler decider :=
  directRetainedFigureNineDirectionDescriptorCompilerOfFiniteSource decider
    (directRetainedFigureNineFiniteSourceDescriptorCompilerOfAppenders
      decider clauses markers)

end PeriodicCNFStripReduction
end LeanTrominoes
