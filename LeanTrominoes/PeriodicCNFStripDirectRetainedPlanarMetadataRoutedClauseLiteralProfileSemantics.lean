/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedClauseDescriptorBlockSemantics

/-! # Literal-profile routed-clause source blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedRoutedLiteralProfileStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Extracting semantic finite literal profiles preserves every unindexed
routed-clause block. -/
theorem directRetainedPlanarMetadataRoutedClauseSourceBlocks_eq_profileBlocks
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataRoutedClauseSourceBlocks
        decider symbols =
      directRetainedPlanarMetadataRoutedClauseProfileBlocks
        decider symbols := by
  unfold directRetainedPlanarMetadataRoutedClauseSourceBlocks
    directRetainedPlanarMetadataRoutedClauseProfileBlocks
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro clause _
  exact (routedClauseDescriptorBlockOfProfiles_literalProfiles clause).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
