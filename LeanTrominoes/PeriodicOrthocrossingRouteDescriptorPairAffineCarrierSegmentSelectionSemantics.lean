/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentPredicateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSegmentSemantics

/-! # One-segment semantics of the affine carrier candidate scan -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Under the diagonal and route-shape guards, one genuine axis-aligned
segment contributes exactly the nine neighboring copies of its axis bit. -/
theorem Segment.carrierAxisSelection_eq
    (shape : RouteShape) (segment : Segment)
    (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : shape.Matches pair.1)
    (axisAligned : (segment.evalPair pair).IsAxisAligned) :
    predicateListBlocks
        (segment.carrierAxisPredicates shape)
        carrierAxisNeighborBlocks
        (descriptorPairTokens pair) =
      neighborTranslations.map fun _ =>
        (decide (segment.evalPair pair).IsHorizontal, false) := by
  rw [predicateListBlocks_eq]
  simp only [Segment.carrierAxisPredicates, List.map_cons, List.map_nil,
    Predicate.evalTokens_descriptorPairTokens]
  have shapeMatches' :
      shape.Matches (descriptorAt pair .first) := by
    simpa [descriptorAt] using shapeMatches
  rcases axisAligned with horizontal | vertical
  · have notVertical : ¬(segment.evalPair pair).IsVertical := by
      intro vertical
      exact horizontal.2 vertical.1
    simp [carrierAxisNeighborBlocks, selectTruthBlocks, sameEdge,
      shapeMatches', horizontal, notVertical, RouteShape.evalPair_guard]
  · have notHorizontal : ¬(segment.evalPair pair).IsHorizontal := by
      intro horizontal
      exact vertical.2 horizontal.1
    simp [carrierAxisNeighborBlocks, selectTruthBlocks, sameEdge,
      shapeMatches', vertical, notHorizontal, RouteShape.evalPair_guard]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
