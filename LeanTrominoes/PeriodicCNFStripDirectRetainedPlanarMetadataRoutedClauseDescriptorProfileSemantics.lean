/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedClauseCompiledProfileSemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedClauseLiteralProfileSemantics

/-! # Source-profile semantics of direct routed-clause descriptor blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Replacing the source clauses by the already compiled exact finite
profiles preserves the routed-clause block stream. -/
theorem directRetainedPlanarMetadataRoutedClauseSourceBlocks_eq_compiled
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataRoutedClauseSourceBlocks decider symbols =
      directRetainedPlanarMetadataCompiledRoutedClauseDescriptors
        decider symbols := by
  exact
    (directRetainedPlanarMetadataRoutedClauseSourceBlocks_eq_profileBlocks
      decider symbols).trans
      (directRetainedPlanarMetadataRoutedClauseProfileBlocks_eq_compiled
        decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
