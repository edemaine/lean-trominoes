/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBendClauseDescriptorCompiledCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBendClauseDescriptorSemantics
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Polynomial-time direct retained bend descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedBendCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The retained bend descriptor family is polynomial-time computable from
the encoded direct source input. -/
noncomputable def
    directRetainedPlanarMetadataBendClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataBendClauseDescriptorCompiler decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedPlanarMetadataCompiledBendClauseDescriptors decider)
    (directRetainedPlanarMetadataBendClauseDescriptors decider)
    (fun symbols =>
      (directRetainedPlanarMetadataBendClauseDescriptors_eq_compiled
        decider symbols).symm)
    (directRetainedPlanarMetadataCompiledBendClauseDescriptorsComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
