/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCarrierClauseDescriptorCompiledCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCarrierClauseDescriptorSemantics
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Polynomial-time direct retained carrier descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedCarrierCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The retained carrier descriptor family is polynomial-time computable from
the encoded direct source input. -/
noncomputable def
    directRetainedPlanarMetadataCarrierClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataCarrierClauseDescriptorCompiler decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedPlanarMetadataCompiledCarrierClauseDescriptors decider)
    (directRetainedPlanarMetadataCarrierClauseDescriptors decider)
    (fun symbols =>
      (directRetainedPlanarMetadataCarrierClauseDescriptors_eq_compiled
        decider symbols).symm)
    (directRetainedPlanarMetadataCompiledCarrierClauseDescriptorsComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
