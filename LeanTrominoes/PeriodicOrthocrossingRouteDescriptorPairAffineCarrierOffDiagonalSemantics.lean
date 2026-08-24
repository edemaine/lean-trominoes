/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierShapeOffDiagonalSemantics

/-! # Off-diagonal semantics of affine carrier candidate blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- The complete affine carrier candidate block is empty off the stored
edge-index diagonal. -/
theorem affineCarrierSegmentBitBlock_eq_nil_of_edgeIndex_ne
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    affineCarrierSegmentBitBlock (descriptorPairTokens pair) = [] := by
  unfold affineCarrierSegmentBitBlock carrierSegmentPredicates
    carrierSegmentBitBlocks
  rw [predicateListBlocks_eq, List.map_flatMap,
    carrierSelectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro shape _shapeMember
    rw [← predicateListBlocks_eq]
    exact shape.carrierSegmentSelection_eq_nil_of_edgeIndex_ne
      pair edgeIndexNe
  · intro shape _shapeMember
    simp [RouteShape.carrierSegmentPredicates,
      RouteShape.carrierSegmentBitBlocks,
      Segment.carrierAxisPredicates, carrierAxisNeighborBlocks]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
