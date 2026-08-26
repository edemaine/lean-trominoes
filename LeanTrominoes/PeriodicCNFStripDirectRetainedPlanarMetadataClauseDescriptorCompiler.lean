/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorBlockCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataQuotientClauseDescriptorAssemblyCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataQuotientClauseDescriptorCorrectness

/-! # Direct retained metadata clause-descriptor compilation -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directClauseDescriptorCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The quotient assembly compiles the exact public clause-descriptor stream. -/
noncomputable def
    directRetainedPlanarMetadataClauseDescriptorsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List FormulaShapeDirectionOrdering.Token)
      encoding.Γ FormulaShapeDirectionOrdering.Token id id
      (directRetainedPlanarMetadataClauseDescriptors decider) := by
  have outputEq :
      directRetainedPlanarMetadataQuotientClauseDescriptorAssembly decider =
        directRetainedPlanarMetadataClauseDescriptors decider :=
    funext
      (directRetainedPlanarMetadataQuotientClauseDescriptorAssembly_eq_clauseDescriptors
        decider)
  rw [← outputEq]
  exact
    directRetainedPlanarMetadataQuotientClauseDescriptorAssemblyComputableInPolyTime
      decider

/-- Preserve the encoded source beside its compiled clause descriptors. -/
noncomputable def
    directRetainedPlanarMetadataClauseDescriptorAppender :
    DirectRetainedPlanarMetadataClauseDescriptorAppender decider :=
  RetainedInputAppendPipeline.appendedComputableInPolyTimeOfCompiler
    (directRetainedPlanarMetadataClauseDescriptors decider)
    (directRetainedPlanarMetadataClauseDescriptorsComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
