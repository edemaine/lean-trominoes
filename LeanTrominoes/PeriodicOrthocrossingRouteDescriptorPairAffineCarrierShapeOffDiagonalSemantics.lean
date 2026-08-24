/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierShapeSelectionSemantics

/-! # Off-diagonal semantics of one affine carrier route shape -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Unequal stored edge indices make every segment predicate of one route
shape false. -/
theorem RouteShape.carrierSegmentSelection_eq_nil_of_edgeIndex_ne
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    predicateListBlocks
        shape.carrierSegmentPredicates
        shape.carrierSegmentBitBlocks
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.carrierSegmentPredicates
    RouteShape.carrierSegmentBitBlocks
  rw [List.map_flatMap, carrierSelectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro segment _segmentMember
    have diagonalFalse : carrierSegmentSameEdgeIndex.evalPair pair = false := by
      simp [edgeIndexNe]
    simp [Segment.carrierAxisPredicates, carrierAxisNeighborBlocks,
      Predicate.evalTokens_descriptorPairTokens, evalPair_all,
      diagonalFalse, selectTruthBlocks]
  · intro segment _segmentMember
    simp [Segment.carrierAxisPredicates, carrierAxisNeighborBlocks]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
