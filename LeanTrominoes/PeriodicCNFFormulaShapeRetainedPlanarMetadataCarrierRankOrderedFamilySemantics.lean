/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierFamilySemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRankOrderedDescriptorSemantics

/-! # Rank-ordered compiler semantics for the retained carrier family -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- On valid Theorem 5.2 inputs, the rank-ordered carrier compiler emits
exactly the semantic retained carrier descriptor family. -/
theorem rankOrderedCarrierLinkDescriptorScan_eq_carrierMetadataClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : incidencesWithMetadata formula ≠ []) :
    rankOrderedCarrierLinkDescriptorScan
        (numericRouteDescriptors formula) =
      carrierMetadataClauseDescriptors formula := by
  rw [rankOrderedCarrierLinkDescriptorScan_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  rw [carrierMetadataClauseDescriptors_eq_canonicalBlocks
    formula wellFormed degree isLocal]
  unfold carrierLinkDescriptorScan retainedCarrierLinkBits
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro link _
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
