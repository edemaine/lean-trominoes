/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedBendRepresentativeDescriptors
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedClauseRepresentativeDescriptors
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBaseBendClauseDescriptorSemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBaseRoutedClauseDescriptorSemantics

/-! # Semantic targets of direct quotiented descriptor families -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directQuotientFamilySemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directQuotientFamilySemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct untranslated bend compiler emits exactly the canonical base
bend descriptor family of the direct retained drawing. -/
theorem directRetainedPlanarMetadataBaseBendClauseDescriptors_eq_base
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataBaseBendClauseDescriptors decider symbols =
      baseBendClauseDescriptors
        (directSourceFormula decider symbols) := by
  rw [directRetainedPlanarMetadataBaseBendClauseDescriptors_eq_semantic,
    baseBendClauseDescriptors_eq_canonicalBlocks]
  unfold baseRouteBends
  rw [List.flatMap_assoc]

/-- The direct base routed-clause compiler emits exactly one canonical
descriptor per clause of the direct source formula. -/
theorem directRetainedPlanarMetadataBaseRoutedClauseDescriptors_eq_base
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataBaseRoutedClauseDescriptors decider symbols =
      baseRoutedClauseDescriptors
        (directSourceFormula decider symbols) := by
  rw [directRetainedPlanarMetadataBaseRoutedClauseDescriptors_eq_semantic]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
