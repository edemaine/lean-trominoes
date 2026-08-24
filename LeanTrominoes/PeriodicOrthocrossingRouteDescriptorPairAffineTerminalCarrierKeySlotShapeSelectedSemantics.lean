/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotShapeActivationSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotShapeValueSemantics

/-! # Selected route-shape terminal carrier-key slot semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- A selected route shape's active padded terminal slots are exactly the
semantic terminal keys of all its evaluated neighboring occurrences. -/
theorem RouteShape.terminalCarrierKeyActiveValues_selected_eq
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : shape.Matches pair.1)
    (axisAligned :
      ∀ segment ∈ shape.segments .first,
        (segment.evalPair pair).IsAxisAligned) :
    activeValues
        (shape.carrierSegmentPredicates.map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (shape.terminalCarrierKeyTemplateBlocks pair) =
      occurrenceTerminalCarrierKeys
        ((shape.segments .first).zipIdx.flatMap fun tagged =>
          neighborTranslations.map fun translate =>
            ((⟨pair.1.edgeIndex, tagged.2,
                tagged.1.evalPair pair⟩ : IndexedGridSegment),
              translate)) := by
  rw [shape.terminalCarrierKeyActiveValues_eq
    pair sameEdge shapeMatches axisAligned]
  exact shape.terminalCarrierKeyTemplateValues_eq pair

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
