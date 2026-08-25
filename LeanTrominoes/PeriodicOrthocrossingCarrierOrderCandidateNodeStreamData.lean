/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalAlternativeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeTemplateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalSourceKeyRecipePairData

/-! # Semantic node stream for carrier order-coordinate candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairFieldTags
open RouteDescriptorPairSourceKeyRecipePairs

/-- Repeat one terminal-node block for the four axis/direction alternatives. -/
def Segment.terminalDirectionalCarrierNodeTemplateBlocks
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) : List (List (Template CarrierNode)) :=
  let block := segment.terminalCarrierNodeTemplateBlock pair segmentIndex
  [block, block, block, block]

def RouteShape.terminalDirectionalCarrierNodeTemplateBlocks
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor) :
    List (List (Template CarrierNode)) :=
  (shape.segments .first).zipIdx.flatMap fun tagged =>
    tagged.1.terminalDirectionalCarrierNodeTemplateBlocks pair tagged.2

def terminalDirectionalCarrierNodeTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor) :
    List (List (Template CarrierNode)) :=
  allRouteShapes.flatMap fun shape =>
    shape.terminalDirectionalCarrierNodeTemplateBlocks pair

/-- Padded terminal nodes in the direction-split compiler order. -/
def terminalDirectionalCarrierNodeCandidates
    (pair : RouteDescriptor × RouteDescriptor) : List (Candidate CarrierNode) :=
  candidates
    (terminalDirectionalPredicates.map fun predicate =>
      predicate.evalTokens (descriptorPairTokens pair))
    (terminalDirectionalCarrierNodeTemplateBlocks pair)

/-- Repeat the semantic source-key recipe pairs in the same four-way order. -/
def Segment.terminalDirectionalSourceKeyRecipePairBlocks
    (segment : Segment) (segmentIndex : Nat) : List (List RecipePair) :=
  let block := segment.terminalSourceKeyRecipePairBlock segmentIndex
  [block, block, block, block]

def RouteShape.terminalDirectionalSourceKeyRecipePairBlocks
    (shape : RouteShape) : List (List RecipePair) :=
  (shape.segments .first).zipIdx.flatMap fun tagged =>
    tagged.1.terminalDirectionalSourceKeyRecipePairBlocks tagged.2

def terminalDirectionalSourceKeyRecipePairBlocks :
    List (List RecipePair) :=
  allRouteShapes.flatMap
    RouteShape.terminalDirectionalSourceKeyRecipePairBlocks

/-- Direction-split terminal-node candidates in descriptor-square order. -/
def terminalDirectionalCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) : List (Candidate CarrierNode) :=
  (descriptors ×ˢ descriptors).flatMap
    terminalDirectionalCarrierNodeCandidates

end RouteDescriptorPairAffine

/-- Complete padded node stream aligned with the order-coordinate compiler. -/
def carrierOrderCandidateNodeStream
    (descriptors : List RouteDescriptor) :
    List (PaddedSupportedLastRepresentativeEqualityRows.Candidate
      CarrierNode) :=
  RouteDescriptorPairAffine.terminalDirectionalCarrierNodeCandidateStream
      descriptors ++
    RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream
      descriptors

end LeanTrominoes.PeriodicOrthocrossing
