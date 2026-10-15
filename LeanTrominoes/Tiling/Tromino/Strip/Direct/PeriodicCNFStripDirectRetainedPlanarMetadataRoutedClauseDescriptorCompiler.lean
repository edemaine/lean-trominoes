/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedClauseDescriptorCompiledCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedClauseDescriptorSemantics
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedInputAppendPipeline

/-! # Polynomial-time direct routed-clause descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
