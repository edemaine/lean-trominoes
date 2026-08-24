/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks
import LeanTrominoes.PeriodicOrthocrossingNeighborTranslationsData
import LeanTrominoes.PeriodicOrthocrossingPlanarTerminals
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyActivationData

/-! # Fixed terminal carrier-node templates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

/-- The two terminal nodes of every neighboring occurrence of one evaluated
affine segment. -/
def Segment.terminalCarrierNodeTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment) :
    List (Template CarrierNode) :=
  neighborTranslations.flatMap fun translate =>
    let indexed : IndexedGridSegment :=
      ⟨pair.1.edgeIndex, segmentIndex, segment.evalPair pair⟩
    ([CarrierNode.terminal ⟨indexed, translate, .start⟩,
        CarrierNode.terminal ⟨indexed, translate, .finish⟩] :
      List CarrierNode).map fun node => ⟨node, true⟩

/-- Identical terminal-node blocks aligned with one segment's horizontal and
vertical classification predicates. -/
def Segment.terminalCarrierNodeTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment) :
    List (List (Template CarrierNode)) :=
  let block := segment.terminalCarrierNodeTemplateBlock pair segmentIndex
  [block, block]

/-- Terminal-node template blocks aligned with one route shape's carrier
segment predicates. -/
def RouteShape.terminalCarrierNodeTemplateBlocks
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor) :
    List (List (Template CarrierNode)) :=
  (shape.segments .first).zipIdx.flatMap fun tagged =>
    tagged.1.terminalCarrierNodeTemplateBlocks pair tagged.2

/-- Complete fixed terminal-node template list aligned with
`carrierSegmentPredicates`. -/
def terminalCarrierNodeTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor) :
    List (List (Template CarrierNode)) :=
  allRouteShapes.flatMap fun shape =>
    shape.terminalCarrierNodeTemplateBlocks pair

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
