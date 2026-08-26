/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataNormalizedRoutedVariableDescriptorSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceSplitRouteDescriptors

/-! # Direct normalized routed-variable descriptor quotient -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directNormalizedRoutedVariableQuotientStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directNormalizedRoutedVariableQuotientVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct compiler's normalized routed-variable descriptor stream has
one complete three-arm site for every literal occurrence of the width-three
source, in presentation order. -/
theorem
    directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors_eq_fullSites
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors
        decider symbols =
      (List.range (PeriodicCNF.presentationLiteralCount
          (PeriodicThreeCNF.formula
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
              decider symbols)))).flatMap
        (fun _targetIndex => routedVariableFullSiteBlock) := by
  rw [directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors_eq_pairScan]
  rw [directSource_numericRouteDescriptors_eq_splitRouteDescriptors]
  exact
    directSource_normalizedRoutedVariablePairDescriptorScan_eq_fullSites
      decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
