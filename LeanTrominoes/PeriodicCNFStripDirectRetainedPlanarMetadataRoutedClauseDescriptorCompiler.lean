/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedClauseDescriptorCompiledCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedClauseDescriptorSemantics
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Polynomial-time direct routed-clause descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedRoutedClauseCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The retained routed-clause descriptor family is polynomial-time
computable from the encoded direct source input. -/
noncomputable def
    directRetainedPlanarMetadataRoutedClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataRoutedClauseDescriptorCompiler decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedPlanarMetadataCompiledRoutedClauseDescriptors decider)
    (directRetainedPlanarMetadataRoutedClauseDescriptors decider)
    (fun symbols =>
      (directRetainedPlanarMetadataRoutedClauseDescriptors_eq_compiled
        decider symbols).symm)
    (directRetainedPlanarMetadataCompiledRoutedClauseDescriptorsComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
