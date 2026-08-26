/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableEdgeIndexDedup

/-! # Canonical order of deduplicated routed-variable links -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The surviving normalized routed-variable links are ordered exactly by
the canonical final-site route-index fibers. -/
theorem deduplicatedWrappedNormalizedRoutedVariableLinks_formula_routeIndices_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    (deduplicatedWrappedNormalizedRoutedVariableLinks
        (formula source)).map
        wrappedNormalizedRoutedVariableLinkRouteIndex =
      canonicalRoutedVariableEdgeIndexScan source := by
  rw [
    deduplicatedWrappedNormalizedRoutedVariableLinks_routeIndices_eq_scan_dedup]
  exact
    wrappedNormalizedRoutedVariableRouteIndexScan_formula_dedup_eq_canonical
      source positiveOffsets

end PeriodicThreeSATThree
end LeanTrominoes
