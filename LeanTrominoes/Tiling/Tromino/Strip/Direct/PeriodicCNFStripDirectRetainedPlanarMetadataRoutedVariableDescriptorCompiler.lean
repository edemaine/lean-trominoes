/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedVariableDescriptorCompiledCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedVariableDescriptorSemantics
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedInputAppendPipeline

/-! # Polynomial-time direct retained routed-variable descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The retained routed-variable descriptor family is polynomial-time
computable from the encoded direct source input. -/
noncomputable def
    directRetainedPlanarMetadataRoutedVariableClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataRoutedVariableClauseDescriptorCompiler decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedPlanarMetadataCompiledRoutedVariableClauseDescriptors
      decider)
    (directRetainedPlanarMetadataRoutedVariableClauseDescriptors decider)
    (fun symbols =>
      (directRetainedPlanarMetadataRoutedVariableClauseDescriptors_eq_compiled
        decider symbols).symm)
    (directRetainedPlanarMetadataCompiledRoutedVariableClauseDescriptorsComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
