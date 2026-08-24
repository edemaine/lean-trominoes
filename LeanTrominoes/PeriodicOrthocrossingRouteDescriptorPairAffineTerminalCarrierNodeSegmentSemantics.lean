/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentSelectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeSlotData

/-! # One-segment terminal carrier-node candidate semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- Exactly one axis predicate is active on a genuine axis-aligned segment,
so removing inactive slots leaves its terminal-node template block. -/
theorem Segment.terminalCarrierNodeActiveValues_eq
    (shape : RouteShape) (segment : Segment) (segmentIndex : Nat)
    (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : shape.Matches pair.1)
    (axisAligned : (segment.evalPair pair).IsAxisAligned) :
    activeValues
        ((segment.carrierAxisPredicates shape).map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (segment.terminalCarrierNodeTemplateBlocks
          pair segmentIndex) =
      (segment.terminalCarrierNodeTemplateBlock
        pair segmentIndex).map Template.value := by
  have shapeMatches' :
      shape.Matches (descriptorAt pair .first) := by
    simpa [descriptorAt] using shapeMatches
  rcases axisAligned with horizontal | vertical
  · have notVertical : ¬(segment.evalPair pair).IsVertical := by
      intro vertical
      exact horizontal.2 vertical.1
    simp [Segment.carrierAxisPredicates,
      Segment.terminalCarrierNodeTemplateBlocks,
      activeValues, sameEdge, shapeMatches', horizontal, notVertical,
      Predicate.evalTokens_descriptorPairTokens,
      RouteShape.evalPair_guard]
  · have notHorizontal : ¬(segment.evalPair pair).IsHorizontal := by
      intro horizontal
      exact vertical.2 horizontal.1
    simp [Segment.carrierAxisPredicates,
      Segment.terminalCarrierNodeTemplateBlocks,
      activeValues, sameEdge, shapeMatches', vertical, notHorizontal,
      Predicate.evalTokens_descriptorPairTokens,
      RouteShape.evalPair_guard]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
