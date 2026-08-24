/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNumericDescriptorScanSemantics
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableSemanticNumericArmScan

/-! # Descriptor expansion of split semantic occurrence arms -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Under the current/next-slice invariant, expanding the semantic numeric
occurrence-arm scan gives the exact numeric split-descriptor scan. -/
theorem routedVariableNumericOccurrenceDescriptorScan_formula_eq_numeric
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    routedVariableSiteArmDescriptorStream
        (routedVariableNumericOccurrenceSiteArmScan (formula source)) =
      routedVariableNumericDescriptorScan
        (splitRouteDescriptors source)
        (PeriodicCNF.presentationLiteralCount source) := by
  rw [routedVariableNumericOccurrenceSiteArmScan_formula_eq_numeric
    source positiveOffsets]
  exact routedVariableNumericSiteArmScan_descriptorStream _ _

end LeanTrominoes.PeriodicThreeSATThree
