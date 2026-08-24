/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceBoundarySiteArmScanBridge
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableSemanticArmScanFactorization
import LeanTrominoes.PeriodicThreeSATThreeSplitCycleSiteArmScan
import LeanTrominoes.PeriodicThreeSATThreeSplitNumericBoundarySiteArmScan

/-! # Semantic and numeric routed-variable arm scans coincide -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- For current/next-slice copied incidences, semantic site order and numeric
split-descriptor target order yield exactly the same routed-variable arms. -/
theorem routedVariableNumericOccurrenceSiteArmScan_formula_eq_numeric
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    routedVariableNumericOccurrenceSiteArmScan (formula source) =
      routedVariableNumericSiteArmScan
        (splitRouteDescriptors source)
        (PeriodicCNF.presentationLiteralCount source) := by
  rw [routedVariableNumericOccurrenceSiteArmScan_formula_eq_blocks
    source positiveOffsets]
  unfold routedVariableNumericSiteArmScan
  rw [splitRouteDescriptors_numericBoundarySiteArmBlocks,
    occurrenceRouteDescriptors_boundarySiteArmBlocks_eq_incidences,
    rotatedOccurrenceVariables_cycleSiteArmBlocks_eq_numeric]

end LeanTrominoes.PeriodicThreeSATThree
