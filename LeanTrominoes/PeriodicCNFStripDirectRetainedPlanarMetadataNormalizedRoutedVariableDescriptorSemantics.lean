/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedVariablePairCompiledSemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataNormalizedRoutedVariableDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagSemantics

/-! # Semantics of direct normalized routed-variable descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directNormalizedRoutedVariableSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directNormalizedRoutedVariableSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled tagged stream is the normalized semantic pair scan of the
direct source's numeric route descriptors. -/
theorem
    directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors_eq_pairScan
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors
        decider symbols =
      normalizedRoutedVariablePairDescriptorScan
        (numericRouteDescriptors
          (directSourceFormula decider symbols)) := by
  unfold
    directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors
  rw [directSourceRouteDescriptorPairFieldTags_eq]
  exact
    compiledNormalizedRoutedVariablePairDescriptorStream_descriptorSquare _

end LeanTrominoes.PeriodicCNFStripReduction

end
