/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataVariableMarkerCompiler

/-! # Concrete direct retained metadata descriptor compilation -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directMetadataConcreteCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Recover the retained source and append its exact variable-marker suffix. -/
noncomputable def directRetainedPlanarMetadataVariableMarkerAppender :
    DirectRetainedPlanarMetadataVariableMarkerAppender decider :=
  RetainedInputAppendPipeline.appendFromWorkspaceComputableInPolyTimeOfCompiler
    (directRetainedPlanarMetadataVariableMarkers decider)
    (directRetainedPlanarMetadataVariableMarkersComputableInPolyTime decider)

/-- The concrete clause and variable passes compile the complete finite
metadata descriptor stream. -/
noncomputable def
    directRetainedPlanarMetadataDirectionDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataDirectionDescriptorCompiler decider :=
  directRetainedPlanarMetadataDirectionDescriptorCompilerOfAppenders decider
    (directRetainedPlanarMetadataClauseDescriptorAppender decider)
    (directRetainedPlanarMetadataVariableMarkerAppender decider)

/-- The concrete metadata compiler also supplies the exact fixed-eight
direction expansion. -/
noncomputable def
    directRetainedFixedEightDirectionDescriptorsComputableInPolyTimeOfBlocks :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List FormulaShapeDirectionOrdering.Token)
      encoding.Γ FormulaShapeDirectionOrdering.Token id id
      (directRetainedFixedEightDirectionDescriptors decider) :=
  directRetainedFixedEightDirectionDescriptorsComputableInPolyTimeOfMetadataAppenders
    decider
    (directRetainedPlanarMetadataClauseDescriptorAppender decider)
    (directRetainedPlanarMetadataVariableMarkerAppender decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
