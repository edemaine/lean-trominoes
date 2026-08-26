/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBaseRoutedClauseDescriptorData
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2CompositionMachine

/-! # Compiling normalized routed-clause descriptor blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedBaseRoutedCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

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
