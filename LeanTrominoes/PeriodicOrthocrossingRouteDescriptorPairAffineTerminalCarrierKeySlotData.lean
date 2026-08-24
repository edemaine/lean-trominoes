/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentScanData

/-! # Fixed terminal carrier-key slots for route-descriptor pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

abbrev CarrierKey := Nat × Nat × Cell

/-- The two terminal-key copies of every neighboring occurrence of one
evaluated affine segment.  Every active terminal key is supported. -/
def Segment.terminalCarrierKeyTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (_segment : Segment) :
    List (Template CarrierKey) :=
  neighborTranslations.flatMap fun translate =>
    let key : CarrierKey :=
      (pair.1.edgeIndex, segmentIndex, translate)
    List.replicate 2 ⟨key, true⟩

/-- Identical terminal-key blocks aligned with one segment's horizontal and
vertical classification predicates. -/
def Segment.terminalCarrierKeyTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment) :
    List (List (Template CarrierKey)) :=
  let block := segment.terminalCarrierKeyTemplateBlock pair segmentIndex
  [block, block]

/-- Terminal-key template blocks aligned with one route shape's carrier
segment predicates. -/
def RouteShape.terminalCarrierKeyTemplateBlocks
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor) :
    List (List (Template CarrierKey)) :=
  (shape.segments .first).zipIdx.flatMap fun tagged =>
    tagged.1.terminalCarrierKeyTemplateBlocks pair tagged.2

/-- Complete fixed terminal-key template list aligned with
`carrierSegmentPredicates`. -/
def terminalCarrierKeyTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor) :
    List (List (Template CarrierKey)) :=
  allRouteShapes.flatMap fun shape =>
    shape.terminalCarrierKeyTemplateBlocks pair

/-- One activation bit per fixed terminal-key template block. -/
def terminalCarrierKeyActivations
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Bool :=
  carrierSegmentPredicates.map fun predicate =>
    predicate.evalTokens tokens

/-- Padded terminal carrier-key slots of one descriptor pair. -/
def paddedTerminalCarrierKeyCandidates
    (pair : RouteDescriptor × RouteDescriptor) :
    List (PaddedSupportedLastRepresentativeEqualityRows.Candidate CarrierKey) :=
  candidates
    (terminalCarrierKeyActivations (descriptorPairTokens pair))
    (terminalCarrierKeyTemplateBlocks pair)

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
