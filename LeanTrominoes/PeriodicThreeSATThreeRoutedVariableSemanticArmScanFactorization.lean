/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSemanticSiteArmScanData
import LeanTrominoes.PeriodicThreeSATThreeVariableRouteBoundarySiteArmScan
import LeanTrominoes.PeriodicThreeSATThreeVariableRouteCycleSiteArmScan
import LeanTrominoes.PeriodicThreeSATThreeVariableRouteSiteOrder

/-! # Boundary/cycle factorization of the semantic split arm scan -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The semantic numeric-arm scan factors into its next-slice boundary
prefix and one current/next cycle block per rotated occurrence atom. -/
theorem routedVariableNumericOccurrenceSiteArmScan_formula_eq_blocks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    routedVariableNumericOccurrenceSiteArmScan (formula source) =
      ((occurrenceIncidences source).flatMap fun incidence =>
        if incidence.edge.offset = (1, 0) then
          routedVariableNextBoundarySiteArmBlocks
        else []) ++
      (rotatedOccurrenceVariables source).flatMap
        (routedVariableCycleSiteArmBlocksAtAtom source) := by
  unfold routedVariableNumericOccurrenceSiteArmScan
  rw [drawingVariableRouteSites_formula_eq_boundary_append_rotated
    source positiveOffsets]
  rw [List.map_append,
    occurrenceBoundaryVariableRouteSites_numericArms_eq,
    rotatedVariableRouteSiteBlocks_numericArms_eq
      source positiveOffsets]

end LeanTrominoes.PeriodicThreeSATThree
