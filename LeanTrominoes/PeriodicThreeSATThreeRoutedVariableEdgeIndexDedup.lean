/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableRouteIndexScanSemantics
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableBoundaryEdgeIndexCoverage

/-! # Deduplicated routed-variable edge indices after occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Stable deduplication of the complete routed-variable route-index scan
retains exactly one final-site fiber per positional occurrence atom, in
rotated target order. -/
theorem wrappedNormalizedRoutedVariableRouteIndexScan_formula_dedup_eq_canonical
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    (wrappedNormalizedRoutedVariableRouteIndexScan
        (formula source)).dedup =
      canonicalRoutedVariableEdgeIndexScan source := by
  rw [wrappedNormalizedRoutedVariableRouteIndexScan_eq_occurrenceEdgeIndices]
  rw [drawingVariableRouteSites_formula_eq_boundary_append_rotated
    source positiveOffsets]
  rw [List.flatMap_append]
  change (boundaryRoutedVariableEdgeIndexScan source ++
      ((rotatedVariableRouteSiteBlocks source).flatMap fun site =>
        ((variableRouteOccurrencesAt (formula source) site).take 3).map
          CNFRouteOccurrence.edgeIndex)).dedup = _
  have boundarySubsetRotated : boundaryRoutedVariableEdgeIndexScan source ⊆
      (rotatedVariableRouteSiteBlocks source).flatMap fun site =>
        ((variableRouteOccurrencesAt (formula source) site).take 3).map
          CNFRouteOccurrence.edgeIndex := by
    intro edgeIndex edgeIndexMember
    have canonicalMember :=
      boundaryRoutedVariableEdgeIndexScan_subset_canonical
        source positiveOffsets edgeIndexMember
    rw [← rotatedVariableRouteSiteBlocks_edgeIndices_dedup_eq_canonical
      source positiveOffsets] at canonicalMember
    exact List.mem_dedup.mp canonicalMember
  rw [boundarySubsetRotated.dedup_append_right]
  exact rotatedVariableRouteSiteBlocks_edgeIndices_dedup_eq_canonical
    source positiveOffsets

end PeriodicThreeSATThree
end LeanTrominoes
