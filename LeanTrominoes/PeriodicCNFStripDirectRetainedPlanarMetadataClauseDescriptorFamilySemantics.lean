/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyData

/-! # Exact direct retained clause-descriptor family decomposition -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directRetainedClauseFamilySemanticsVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

theorem directRetainedPlanarMetadataClauseDescriptorCandidates_eq_families
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataClauseDescriptorCandidates decider symbols =
      directRetainedPlanarMetadataFamilyClauseDescriptors decider symbols := by
  simpa only [directRetainedPlanarMetadataClauseDescriptorCandidates,
    directRetainedPlanarMetadataFamilyClauseDescriptors] using
    FormulaShapeRetainedPlanarMetadataDirection.metadataClauseDescriptorCandidates_eq_families
      (directSourceFormula decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
