/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataBaseRoutedClauseDescriptorData
import LeanTrominoes.Computation.Encoding.Finite.FiniteBlockTransducer
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Compiling normalized routed-clause descriptor blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Exact source clause profiles compose with a finite one-token block map. -/
noncomputable def
    directRetainedPlanarMetadataBaseRoutedClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataBaseRoutedClauseDescriptorCompiler decider := by
  let profiles := directSourceFormulaClauseProfilesComputableInPolyTime
    decider
  let descriptors := FiniteBlockTransducer.computableInPolyTime
    directRetainedPlanarMetadataBaseRoutedClauseDescriptorBlock
  let complete :=
    TM2CompositionMachine.computableInPolyTime profiles descriptors
  change @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
    encoding.Γ PeriodicCNF.FormulaShapeDirectionOrdering.Token id id
    (fun symbols =>
      (directSourceFormulaClauseProfiles decider symbols).flatMap
        directRetainedPlanarMetadataBaseRoutedClauseDescriptorBlock)
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction

end
