/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeShapeActivationSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeValueSemantics

/-! # Selected route-shape terminal carrier-node semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- A selected route shape's active padded terminal slots are exactly the
semantic terminal nodes of all its evaluated neighboring occurrences. -/
theorem RouteShape.terminalCarrierNodeActiveValues_selected_eq
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
      (((shape.segments .first).zipIdx.flatMap fun tagged =>
          neighborTranslations.map fun translate =>
            ((⟨pair.1.edgeIndex, tagged.2,
                tagged.1.evalPair pair⟩ : IndexedGridSegment),
              translate)).flatMap occurrenceCarrierTerminalNodes) := by
  rw [shape.terminalCarrierNodeActiveValues_eq
    pair sameEdge shapeMatches axisAligned]
  exact shape.terminalCarrierNodeTemplateValues_eq pair

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
