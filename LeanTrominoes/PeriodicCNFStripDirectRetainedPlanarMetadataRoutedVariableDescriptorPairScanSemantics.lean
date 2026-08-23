/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairStreamSemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedVariableDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagSemantics

/-! # Numeric pair-scan semantics of direct routed-variable descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedRoutedVariablePairScanStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directRetainedRoutedVariablePairScanVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct compiled output is exactly the semantic row-major scan of the
numeric incidence-route descriptor square. -/
theorem directRetainedPlanarMetadataCompiledRoutedVariableClauseDescriptors_eq_pairScan
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataCompiledRoutedVariableClauseDescriptors
        decider symbols =
      FormulaShapeRetainedPlanarMetadataDirection.routedVariablePairDescriptorScan
        (numericRouteDescriptors (directSourceFormula decider symbols)) := by
  unfold directRetainedPlanarMetadataCompiledRoutedVariableClauseDescriptors
  rw [directSourceRouteDescriptorPairFieldTags_eq,
    FormulaShapeRetainedPlanarMetadataDirection.compiledRoutedVariablePairDescriptorStream_descriptorSquare]

end LeanTrominoes.PeriodicCNFStripReduction

end
