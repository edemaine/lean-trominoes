/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierNodeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeTemplateData

/-! # Values of terminal carrier-node templates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

/-- One segment template block lists the two semantic terminal nodes of each
neighboring occurrence, in translation-major order. -/
theorem Segment.terminalCarrierNodeTemplateBlock_values
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) :
    (segment.terminalCarrierNodeTemplateBlock
        pair segmentIndex).map Template.value =
      neighborTranslations.flatMap fun translate =>
        occurrenceCarrierTerminalNodes
          ((⟨pair.1.edgeIndex, segmentIndex,
              segment.evalPair pair⟩ : IndexedGridSegment),
            translate) := by
  unfold Segment.terminalCarrierNodeTemplateBlock
    occurrenceCarrierTerminalNodes occurrenceTerminals
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro translate _translateMember
  rfl

/-- Flattening one route shape's terminal template values gives the semantic
terminal nodes of all its evaluated neighboring occurrences. -/
theorem RouteShape.terminalCarrierNodeTemplateValues_eq
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor) :
    ((shape.segments .first).zipIdx.flatMap fun tagged =>
        (tagged.1.terminalCarrierNodeTemplateBlock
          pair tagged.2).map Template.value) =
      (((shape.segments .first).zipIdx.flatMap fun tagged =>
          neighborTranslations.map fun translate =>
            ((⟨pair.1.edgeIndex, tagged.2,
                tagged.1.evalPair pair⟩ : IndexedGridSegment),
              translate)).flatMap occurrenceCarrierTerminalNodes) := by
  rw [show
      ((shape.segments .first).zipIdx.flatMap fun tagged =>
          (tagged.1.terminalCarrierNodeTemplateBlock
            pair tagged.2).map Template.value) =
        (shape.segments .first).zipIdx.flatMap fun tagged =>
          (neighborTranslations.map fun translate =>
            ((⟨pair.1.edgeIndex, tagged.2,
                tagged.1.evalPair pair⟩ : IndexedGridSegment),
              translate)).flatMap occurrenceCarrierTerminalNodes by
    apply List.flatMap_congr
    intro tagged _taggedMember
    exact tagged.1.terminalCarrierNodeTemplateBlock_values
      pair tagged.2]
  rw [List.flatMap_assoc]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
