/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClausePresentationSemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedClauseDescriptorProfileSemantics

/-! # Correctness of direct routed-clause descriptor blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedRoutedClauseSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedRoutedClauseSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directRetainedClauseFamilyDataVariableDecidableEq

/-- The finite profile transducer emits exactly the retained routed-clause
descriptor family of the direct geometric source. -/
theorem directRetainedPlanarMetadataRoutedClauseDescriptors_eq_compiled
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataRoutedClauseDescriptors decider symbols =
      directRetainedPlanarMetadataCompiledRoutedClauseDescriptors
        decider symbols := by
  let source := directSourceFormula decider symbols
  calc
    directRetainedPlanarMetadataRoutedClauseDescriptors decider symbols =
        directRetainedPlanarMetadataRoutedClauseSourceBlocks
          decider symbols := by
      simpa only [directRetainedPlanarMetadataRoutedClauseDescriptors,
        directRetainedPlanarMetadataRoutedClauseSourceBlocks, source] using
        FormulaShapeRetainedPlanarMetadataDirection.routedClauseMetadataClauseDescriptors_eq_sourceClauses
          source (PeriodicCNF.incidenceGraph_isWellFormed source)
    _ = _ :=
      directRetainedPlanarMetadataRoutedClauseSourceBlocks_eq_compiled
        decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
