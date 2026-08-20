/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorBlocks
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorCompiler
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Two-pass direct retained metadata descriptor compilation -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedMetadataBlockCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- First retained-input pass: preserve source symbols and append every
deduplicated metadata clause descriptor. -/
abbrev DirectRetainedPlanarMetadataClauseDescriptorAppender :=
  TM2ComputableInPolyTime id id
    (RetainedInputAppendPipeline.appended
      (directRetainedPlanarMetadataClauseDescriptors decider))

/-- Second retained-input pass: recover the preserved source symbols and
append the exact distinct-variable marker suffix. -/
abbrev DirectRetainedPlanarMetadataVariableMarkerAppender :=
  TM2ComputableInPolyTime id id
    (RetainedInputAppendPipeline.appendFromWorkspace
      (directRetainedPlanarMetadataVariableMarkers decider))

/-- Independently verified clause and variable passes compose to the exact
finite metadata descriptor compiler. -/
noncomputable def
    directRetainedPlanarMetadataDirectionDescriptorCompilerOfAppenders
    (clauses :
      DirectRetainedPlanarMetadataClauseDescriptorAppender decider)
    (markers :
      DirectRetainedPlanarMetadataVariableMarkerAppender decider) :
    DirectRetainedPlanarMetadataDirectionDescriptorCompiler decider := by
  exact RetainedInputAppendPipeline.computableInPolyTimeOfAppendersEq
    (directRetainedPlanarMetadataClauseDescriptors decider)
    (directRetainedPlanarMetadataVariableMarkers decider)
    (directRetainedPlanarMetadataDirectionDescriptors decider)
    (fun symbols =>
      (directRetainedPlanarMetadataDirectionDescriptors_eq_blocks
        decider symbols).symm)
    clauses markers

/-- The same pair of passes supplies the already verified exact fixed-eight
descriptor expansion. -/
noncomputable def
    directRetainedFixedEightDirectionDescriptorsComputableInPolyTimeOfMetadataAppenders
    (clauses :
      DirectRetainedPlanarMetadataClauseDescriptorAppender decider)
    (markers :
      DirectRetainedPlanarMetadataVariableMarkerAppender decider) :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List FormulaShapeDirectionOrdering.Token)
      encoding.Γ FormulaShapeDirectionOrdering.Token
      id id (directRetainedFixedEightDirectionDescriptors decider) :=
  directRetainedFixedEightDirectionDescriptorsComputableInPolyTimeOfMetadata
    decider
    (directRetainedPlanarMetadataDirectionDescriptorCompilerOfAppenders
      decider clauses markers)

end PeriodicCNFStripReduction
end LeanTrominoes
