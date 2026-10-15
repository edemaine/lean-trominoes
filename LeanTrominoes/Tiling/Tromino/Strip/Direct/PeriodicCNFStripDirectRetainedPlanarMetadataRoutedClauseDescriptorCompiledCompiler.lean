/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedClauseDescriptorData
import LeanTrominoes.Computation.Encoding.Finite.FiniteBlockTransducer
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Compiling finite routed-clause descriptor blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Compile exact source clause profiles, then expand each finite profile to
its fixed nine-site routed descriptor block. -/
noncomputable def
    directRetainedPlanarMetadataCompiledRoutedClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataCompiledRoutedClauseDescriptorCompiler
      decider := by
  let profiles := directSourceFormulaClauseProfilesComputableInPolyTime
    decider
  let descriptors := FiniteBlockTransducer.computableInPolyTime
    directRetainedPlanarMetadataRoutedClauseDescriptorBlock
  let complete := TM2CompositionMachine.computableInPolyTime
    profiles descriptors
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction

end
