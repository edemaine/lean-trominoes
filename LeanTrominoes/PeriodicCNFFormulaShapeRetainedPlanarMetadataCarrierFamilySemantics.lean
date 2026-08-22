/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierDescriptorSemantics

/-! # Complete retained carrier descriptor-family semantics -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The complete retained carrier family is a finite two-token expansion of
the selected carrier links.  Only each link's axis and normalized next-slice
bit remain. -/
theorem carrierMetadataClauseDescriptors_eq_canonicalBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    carrierMetadataClauseDescriptors source =
      (retainedDrawingCompleteCarrierLinks source.incidenceGraph).flatMap
        fun link =>
          canonicalCarrierLinkDescriptorBlock link.first.isHorizontal
            (carrierLinkNextSlice source link) := by
  rw [carrierMetadataClauseDescriptors_eq_flatMap_linkBlocks]
  apply List.flatMap_congr
  intro link linkMember
  exact carrierLinkClauseDescriptors_eq_canonicalBlock
    source wellFormed degree isLocal link linkMember

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
