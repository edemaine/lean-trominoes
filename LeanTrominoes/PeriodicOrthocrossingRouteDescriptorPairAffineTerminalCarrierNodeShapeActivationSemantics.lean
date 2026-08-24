/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeShapeIndexedSemantics

/-! # Route-shape terminal carrier-node activation semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- The public carrier predicate list has the same activation order as the
indexed terminal-node template blocks. -/
theorem RouteShape.terminalCarrierNodeActiveValues_eq
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : shape.Matches pair.1)
    (axisAligned :
      ∀ segment ∈ shape.segments .first,
        (segment.evalPair pair).IsAxisAligned) :
    activeValues
        (shape.carrierSegmentPredicates.map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (shape.terminalCarrierNodeTemplateBlocks pair) =
      (shape.segments .first).zipIdx.flatMap fun tagged =>
        (tagged.1.terminalCarrierNodeTemplateBlock
          pair tagged.2).map Template.value := by
  have predicateMapEq :
      (shape.carrierSegmentPredicates.map fun predicate =>
        predicate.evalTokens (descriptorPairTokens pair)) =
        (shape.segments .first).zipIdx.flatMap fun tagged =>
          (tagged.1.carrierAxisPredicates shape).map fun predicate =>
            predicate.evalTokens (descriptorPairTokens pair) := by
    unfold RouteShape.carrierSegmentPredicates
    rw [List.map_flatMap]
    conv_lhs =>
      rw [← List.zipIdx_map_fst 0 (shape.segments .first),
        List.flatMap_map]
  rw [predicateMapEq]
  exact shape.terminalCarrierNodeActiveValues_zipIdx_eq
    pair sameEdge shapeMatches axisAligned

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
