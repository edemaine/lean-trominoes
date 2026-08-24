/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockAppend
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentPredicateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeSlotData

/-! # Off-diagonal route-shape terminal carrier-node candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- Unequal stored edge indices make every terminal-node slot of one route
shape inactive. -/
theorem RouteShape.terminalCarrierNodeActiveValues_eq_nil_of_edgeIndex_ne
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    activeValues
        (shape.carrierSegmentPredicates.map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (shape.terminalCarrierNodeTemplateBlocks pair) = [] := by
  have activationsEq :
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
  rw [activationsEq]
  unfold RouteShape.terminalCarrierNodeTemplateBlocks
  rw [activeValues_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro tagged _taggedMember
    have diagonalFalse :
        carrierSegmentSameEdgeIndex.evalPair pair = false := by
      simp [edgeIndexNe]
    simp [Segment.carrierAxisPredicates,
      Segment.terminalCarrierNodeTemplateBlocks,
      Predicate.evalTokens_descriptorPairTokens, evalPair_all,
      diagonalFalse, activeValues]
  · intro tagged _taggedMember
    simp [Segment.carrierAxisPredicates,
      Segment.terminalCarrierNodeTemplateBlocks]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
