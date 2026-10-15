/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataBendClauseDescriptorCompiledCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataBendClauseDescriptorSemantics
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedInputAppendPipeline

/-! # Polynomial-time direct retained bend descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
