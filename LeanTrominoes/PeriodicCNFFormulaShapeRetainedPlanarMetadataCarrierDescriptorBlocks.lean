/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorFamilyData

/-! # Per-link carrier clause-descriptor blocks

Each retained straight-carrier equality link contributes the two implication
clauses of `equalityInstance`.  This file exposes their descriptor block as a
separate local unit and rewrites the complete carrier family as a flat map of
those two-token blocks.
-/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The two local clause descriptors contributed by one retained straight
carrier equality link. -/
def carrierLinkClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode) :
    List FormulaShapeDirectionOrdering.Token :=
  (drawingPlanarSATCarrierClauseMetadataFor
      (Variable := Variable) link).map
    (metadataClauseDescriptor source)

@[simp] theorem carrierLinkClauseDescriptors_length
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode) :
    (carrierLinkClauseDescriptors source link).length = 2 := by
  simp [carrierLinkClauseDescriptors,
    drawingPlanarSATCarrierClauseMetadataFor,
    drawingPlanarSATCarrierFormulaAt, equalityInstance]

/-- The complete retained carrier descriptor family is the presentation-order
concatenation of the two-token block of each selected carrier link. -/
theorem carrierMetadataClauseDescriptors_eq_flatMap_linkBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    carrierMetadataClauseDescriptors source =
      (retainedDrawingCompleteCarrierLinks source.incidenceGraph).flatMap
        (carrierLinkClauseDescriptors source) := by
  unfold carrierMetadataClauseDescriptors
    retainedDrawingPlanarSATCarrierClauseMetadata
  rw [List.map_flatMap]
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
