/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairStreamCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedVariableDescriptorData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Compiling direct retained routed-variable descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Compile exact descriptor-pair fields, then independently scan every pair
for its finite routed-variable descriptor block. -/
noncomputable def
    directRetainedPlanarMetadataCompiledRoutedVariableClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataCompiledRoutedVariableClauseDescriptorCompiler
      decider := by
  let fields :=
    directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider
  let descriptors :=
    PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.compiledRoutedVariablePairDescriptorStreamComputableInPolyTime
  let complete := TM2CompositionMachine.computableInPolyTime
    fields descriptors
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction

end
