/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockAppend
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotSegmentSemantics

/-! # One-shape terminal carrier-key slot semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- Removing inactive terminal-key slots from one selected route shape
leaves one terminal-key block for every evaluated segment, in indexed
segment order. -/
theorem RouteShape.terminalCarrierKeyActiveValues_zipIdx_eq
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : shape.Matches pair.1)
    (axisAligned :
      ∀ segment ∈ shape.segments .first,
        (segment.evalPair pair).IsAxisAligned) :
    activeValues
        ((shape.segments .first).zipIdx.flatMap fun tagged =>
          (tagged.1.carrierAxisPredicates shape).map fun predicate =>
            predicate.evalTokens (descriptorPairTokens pair))
        (shape.terminalCarrierKeyTemplateBlocks pair) =
      (shape.segments .first).zipIdx.flatMap fun tagged =>
        (tagged.1.terminalCarrierKeyTemplateBlock
          pair tagged.2).map Template.value := by
  unfold RouteShape.terminalCarrierKeyTemplateBlocks
  rw [activeValues_flatMap]
  · apply List.flatMap_congr
    intro tagged taggedMember
    exact tagged.1.terminalCarrierKeyActiveValues_eq
      shape tagged.2 pair sameEdge shapeMatches
      (axisAligned tagged.1
        (List.fst_mem_of_mem_zipIdx taggedMember))
  · intro tagged _taggedMember
    simp [Segment.carrierAxisPredicates,
      Segment.terminalCarrierKeyTemplateBlocks]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
