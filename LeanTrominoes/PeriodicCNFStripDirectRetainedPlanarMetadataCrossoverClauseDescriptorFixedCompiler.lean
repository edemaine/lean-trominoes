/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossoverClauseDescriptorCompiledCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossoverClauseDescriptorSemantics
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Polynomial-time fixed crossover descriptor blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedCrossoverFixedCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def
    directRetainedPlanarMetadataFixedCrossoverClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataFixedCrossoverClauseDescriptorCompiler
      decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedPlanarMetadataCompiledCrossoverClauseDescriptors decider)
    (directRetainedPlanarMetadataFixedCrossoverClauseDescriptors decider)
    (directRetainedPlanarMetadataCompiledCrossoverClauseDescriptors_eq_fixed
      decider)
    (directRetainedPlanarMetadataCompiledCrossoverClauseDescriptorsComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
