/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNumericDescriptorScanSemantics
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariablePairNumericDescriptorScan
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableSemanticNumericArmScan

/-! # Semantic routed-variable arms as the split descriptor-pair scan -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- For occurrence-split inputs with current/next-slice copied incidences,
expanding the semantic numeric arm scan is exactly the row-major descriptor
pair scan. -/
theorem routedVariableNumericOccurrenceSiteArmStream_formula_eq_pairScan
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    routedVariableSiteArmDescriptorStream
        (routedVariableNumericOccurrenceSiteArmScan (formula source)) =
      routedVariablePairDescriptorScan (splitRouteDescriptors source) := by
  rw [routedVariableNumericOccurrenceSiteArmScan_formula_eq_numeric
    source positiveOffsets]
  rw [routedVariableNumericSiteArmScan_descriptorStream]
  exact
    (routedVariablePairDescriptorScan_splitRouteDescriptors_eq_numeric
      source).symm

end LeanTrominoes.PeriodicThreeSATThree
