/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRankOrderedDescriptorData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRankOrderedPairSemantics

/-! # Exact semantics of rank-ordered retained carrier-link descriptors -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- On valid Theorem 5.2 inputs, the compiled rank-ordered descriptor scan is
exactly the fixed descriptor expansion of the semantic retained carrier-link
stream. -/
theorem rankOrderedCarrierLinkDescriptorScan_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : incidencesWithMetadata formula ≠ []) :
    rankOrderedCarrierLinkDescriptorScan
        (numericRouteDescriptors formula) =
      carrierLinkDescriptorScan
        (retainedCarrierLinkBits formula.incidenceGraph
          (carrierLinkNextSlice formula)) := by
  unfold rankOrderedCarrierLinkDescriptorScan
  rw [retainedPairBits_numericRouteDescriptors_eq_retainedCarrierLinkBits
    formula wellFormed degree isLocal forward nonempty]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
