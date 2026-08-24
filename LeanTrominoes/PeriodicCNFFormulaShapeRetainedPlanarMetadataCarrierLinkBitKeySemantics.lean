/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierLinkBitData
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierRepresentativeKeySemantics

/-! # Per-key presentation of retained carrier-link bits -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Presentation-order carrier-link bits belonging to one physical carrier
key. -/
def retainedCarrierLinkBitsAt
    {Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (nextSlice : EqualityLink CarrierNode → Bool)
    (key : Nat × Nat × Cell) : List (Bool × Bool) :=
  (retainedRepresentativeCarrierLinksAt graph key).map fun link =>
    (link.first.isHorizontal, nextSlice link)

/-- The exact global retained-link bit order is the retained neighboring-key
order, with each key expanded to its representative-link bit block. -/
theorem retainedCarrierLinkBits_eq_keyBlocks
    {Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (nextSlice : EqualityLink CarrierNode → Bool) :
    retainedCarrierLinkBits graph nextSlice =
      (retainedNeighboringCarrierKeys graph).flatMap
        (retainedCarrierLinkBitsAt graph nextSlice) := by
  unfold retainedCarrierLinkBits
  rw [retainedDrawingCompleteCarrierLinks_eq_neighboring]
  unfold retainedNeighboringCarrierLinks retainedCarrierLinkBitsAt
  rw [List.map_flatMap]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
