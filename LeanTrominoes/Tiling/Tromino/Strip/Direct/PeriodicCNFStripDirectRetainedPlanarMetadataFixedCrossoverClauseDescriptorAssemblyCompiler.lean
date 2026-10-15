/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataBendClauseDescriptorCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataCarrierClauseDescriptorCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorCarrierSuffixCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataCrossoverClauseDescriptorFixedCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataFixedCrossoverClauseDescriptorAssemblyData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedClauseDescriptorCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedVariableDescriptorCompiler

/-! # Compiling the fixed-crossover descriptor assembly -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Compile the fixed crossover prefix and all four ordered non-crossover
descriptor scans, then append the two outputs. -/
noncomputable def
    directRetainedPlanarMetadataFixedCrossoverClauseDescriptorAssemblyComputableInPolyTime :
    DirectRetainedPlanarMetadataFixedCrossoverClauseDescriptorAssemblyCompiler
      decider := by
  let routed :=
    directRetainedPlanarMetadataRoutedClauseDescriptorSuffixComputableInPolyTime
      decider
      (directRetainedPlanarMetadataRoutedClauseDescriptorsComputableInPolyTime
        decider)
      (directRetainedPlanarMetadataRoutedVariableClauseDescriptorsComputableInPolyTime
        decider)
  let bent :=
    directRetainedPlanarMetadataBendClauseDescriptorSuffixComputableInPolyTime
      decider
      (directRetainedPlanarMetadataBendClauseDescriptorsComputableInPolyTime
        decider)
      routed
  let carried :=
    directRetainedPlanarMetadataCarrierClauseDescriptorSuffixComputableInPolyTime
      decider
      (directRetainedPlanarMetadataCarrierClauseDescriptorsComputableInPolyTime
        decider)
      bent
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (fun symbols =>
      directRetainedPlanarMetadataFixedCrossoverClauseDescriptors
          decider symbols ++
        directRetainedPlanarMetadataCarrierClauseDescriptorSuffix
          decider symbols)
  exact TM2ListAppend.nativeComputableInPolyTime
    (directRetainedPlanarMetadataFixedCrossoverClauseDescriptorsComputableInPolyTime
      decider)
    carried

end LeanTrominoes.PeriodicCNFStripReduction

end
