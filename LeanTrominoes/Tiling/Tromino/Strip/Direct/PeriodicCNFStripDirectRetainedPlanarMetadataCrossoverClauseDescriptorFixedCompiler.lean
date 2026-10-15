/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataCrossoverClauseDescriptorCompiledCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataCrossoverClauseDescriptorSemantics
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedInputAppendPipeline

/-! # Polynomial-time fixed crossover descriptor blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
