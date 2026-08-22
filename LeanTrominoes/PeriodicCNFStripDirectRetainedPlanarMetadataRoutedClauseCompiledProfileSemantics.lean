/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedClauseDescriptorData

/-! # Compiled profile blocks for direct routed-clause descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedRoutedCompiledProfileStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Exact source clause profiles reproduce the semantic profile-block
stream by a fixed finite block map. -/
theorem directRetainedPlanarMetadataRoutedClauseProfileBlocks_eq_compiled
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataRoutedClauseProfileBlocks decider symbols =
      directRetainedPlanarMetadataCompiledRoutedClauseDescriptors
        decider symbols := by
  let source := directSourceFormula decider symbols
  let sourceProfiles := directSourceFormulaClauseProfiles decider symbols
  let emit :=
    directRetainedPlanarMetadataRoutedClauseDescriptorBlockOfProfiles
  calc
    directRetainedPlanarMetadataRoutedClauseProfileBlocks decider symbols =
        (source.clauses.map
          ClauseProfileOccurrenceSplit.literalProfiles).flatMap emit := by
      rfl
    _ = (sourceProfiles.map ClauseProfile.literals).flatMap emit := by
      rw [directSourceFormulaClauseProfiles_literals_eq decider symbols]
      rfl
    _ = sourceProfiles.flatMap
          directRetainedPlanarMetadataRoutedClauseDescriptorBlock := by
      rw [List.flatMap_map]
      rfl
    _ = directRetainedPlanarMetadataCompiledRoutedClauseDescriptors
          decider symbols := by
      rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
