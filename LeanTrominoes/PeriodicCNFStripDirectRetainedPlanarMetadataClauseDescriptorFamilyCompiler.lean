/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyCompilerBridge
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilySemantics
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Transporting compiled retained families to descriptor candidates -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedClauseFamilyCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The semantic five-family stream is exactly the undeduplicated candidate
stream expected by representative selection. -/
noncomputable def
    directRetainedPlanarMetadataClauseDescriptorCandidateCompilerOfFamily
    (family :
      DirectRetainedPlanarMetadataFamilyClauseDescriptorCompiler decider) :
    DirectRetainedPlanarMetadataClauseDescriptorCandidateCompiler decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedPlanarMetadataFamilyClauseDescriptors decider)
    (directRetainedPlanarMetadataClauseDescriptorCandidates decider)
    (fun symbols =>
      (directRetainedPlanarMetadataClauseDescriptorCandidates_eq_families
        decider symbols).symm)
    family

end PeriodicCNFStripReduction
end LeanTrominoes

end
