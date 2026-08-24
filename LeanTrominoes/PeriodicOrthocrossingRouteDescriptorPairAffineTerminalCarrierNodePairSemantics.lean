/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFlatMapUnique
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeShapeRejectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeShapeSelectedSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelectionSemantics

/-! # Descriptor-pair terminal carrier-node candidate semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- On a diagonal pair with a matching shape, the complete fixed shape scan
retains exactly that shape's neighboring-occurrence terminal nodes. -/
theorem terminalCarrierNodeActiveValues_eq_of_matches
    (selectedShape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : selectedShape.Matches pair.1)
    (axisAligned :
      ∀ segment ∈ selectedShape.segments .first,
        (segment.evalPair pair).IsAxisAligned) :
    activeValues
        (terminalCarrierKeyActivations (descriptorPairTokens pair))
        (terminalCarrierNodeTemplateBlocks pair) =
      (((selectedShape.segments .first).zipIdx.flatMap fun tagged =>
          neighborTranslations.map fun translate =>
            ((⟨pair.1.edgeIndex, tagged.2,
                tagged.1.evalPair pair⟩ : IndexedGridSegment),
              translate)).flatMap occurrenceCarrierTerminalNodes) := by
  unfold terminalCarrierKeyActivations carrierSegmentPredicates
    terminalCarrierNodeTemplateBlocks
  rw [List.map_flatMap, activeValues_flatMap]
  · rw [List.flatMap_eq_selected_of_unique
      allRouteShapes
      (fun shape =>
        activeValues
          (shape.carrierSegmentPredicates.map fun predicate =>
            predicate.evalTokens (descriptorPairTokens pair))
          (shape.terminalCarrierNodeTemplateBlocks pair))
      selectedShape allRouteShapes_nodup
      (mem_allRouteShapes selectedShape)]
    · exact selectedShape.terminalCarrierNodeActiveValues_selected_eq
        pair sameEdge shapeMatches axisAligned
    · intro shape _shapeMember shapeNe
      apply shape.terminalCarrierNodeActiveValues_eq_nil_of_not_matches
      intro otherMatches
      exact shapeNe
        (RouteShape.eq_of_matches otherMatches shapeMatches)
  · intro shape _shapeMember
    simp [RouteShape.carrierSegmentPredicates,
      RouteShape.terminalCarrierNodeTemplateBlocks,
      Segment.carrierAxisPredicates,
      Segment.terminalCarrierNodeTemplateBlocks]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
