/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairScanData
import LeanTrominoes.PeriodicCNFStripDirectSourceSplitRouteDescriptors

/-! # Routed-variable pair scan of direct split sources -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceRoutedVariablePairScanStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Replacing the semantic numeric route stream by its explicit split stream
preserves the pure routed-variable descriptor-pair scan. -/
theorem directSource_routedVariablePairDescriptorScan_eq_split
    (symbols : List encoding.Γ) :
    routedVariablePairDescriptorScan
        (numericRouteDescriptors (directSourceFormula decider symbols)) =
      routedVariablePairDescriptorScan
        (PeriodicThreeSATThree.splitRouteDescriptors
          (PeriodicThreeCNF.formula
            (PolySpaceCompiler.formulaOfSymbols decider symbols))) :=
  congrArg routedVariablePairDescriptorScan
    (directSource_numericRouteDescriptors_eq_splitRouteDescriptors
      decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
