/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorBlockCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataQuotientClauseDescriptorAssemblyCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataQuotientClauseDescriptorCorrectness

/-! # Direct retained metadata clause-descriptor compilation -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
