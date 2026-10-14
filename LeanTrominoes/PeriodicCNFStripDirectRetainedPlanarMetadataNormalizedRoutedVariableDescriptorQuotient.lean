/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataNormalizedRoutedVariableDescriptorSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceSplitRouteDescriptors

/-! # Direct normalized routed-variable descriptor quotient -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
            (PeriodicCNF.ProgramSource.formulaOfSymbols
              decider symbols)))).flatMap
        (fun _targetIndex => routedVariableFullSiteBlock) := by
  rw [directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors_eq_pairScan]
  rw [directSource_numericRouteDescriptors_eq_splitRouteDescriptors]
  exact
    directSource_normalizedRoutedVariablePairDescriptorScan_eq_fullSites
      decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
