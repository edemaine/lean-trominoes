/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataCarrierClauseDescriptorCompiledCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataCarrierClauseDescriptorSemantics
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedInputAppendPipeline

/-! # Polynomial-time direct retained carrier descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
