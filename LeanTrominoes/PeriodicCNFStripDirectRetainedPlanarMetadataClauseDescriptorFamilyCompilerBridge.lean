/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyAssemblerCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyAssemblySemantics
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Compiler bridge to the semantic retained family stream -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable def
    directRetainedPlanarMetadataFamilyClauseDescriptorCompilerOfAssembled
    (assembled :
      DirectRetainedPlanarMetadataAssembledFamilyClauseDescriptorCompiler
        decider) :
    DirectRetainedPlanarMetadataFamilyClauseDescriptorCompiler decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedPlanarMetadataAssembledFamilyClauseDescriptors decider)
    (directRetainedPlanarMetadataFamilyClauseDescriptors decider)
    (directRetainedPlanarMetadataAssembledFamilyClauseDescriptors_eq
      decider)
    assembled

end LeanTrominoes.PeriodicCNFStripReduction

end
