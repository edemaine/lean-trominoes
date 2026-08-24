/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodePairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairOccurrenceTemplateSemantics

/-! # Diagonal descriptor terminal carrier-node candidate semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- On the diagonal of a locally shaped descriptor whose semantic segments
are axis aligned, active slots give its exact neighboring terminal nodes. -/
theorem terminalCarrierNodeActiveValues_diagonal
    (descriptor : RouteDescriptor)
    (hasLocalShape :
      RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape descriptor)
    (axisAligned :
      ∀ segment ∈ gridPolylineSegments descriptor.route,
        segment.IsAxisAligned) :
    activeValues
        (terminalCarrierKeyActivations
          (descriptorPairTokens (descriptor, descriptor)))
        (terminalCarrierNodeTemplateBlocks (descriptor, descriptor)) =
      descriptor.selfIndexedNeighborOccurrences.flatMap
        occurrenceCarrierTerminalNodes := by
  rcases hasLocalShape with ⟨shape, shapeMatches⟩
  have shapeMatches' :
      shape.Matches (descriptorAt (descriptor, descriptor) .first) := by
    simpa [descriptorAt] using shapeMatches
  have segmentsEq := shape.map_evalPair_segments .first
    (descriptor, descriptor) shapeMatches'
  have segmentsEq' :
      (shape.segments .first).map
          (fun segment => segment.evalPair (descriptor, descriptor)) =
        gridPolylineSegments descriptor.route := by
    simpa [descriptorAt] using segmentsEq
  have shapeAxisAligned :
      ∀ segment ∈ shape.segments .first,
        (segment.evalPair (descriptor, descriptor)).IsAxisAligned := by
    intro segment segmentMember
    apply axisAligned
    rw [← segmentsEq']
    exact List.mem_map_of_mem segmentMember
  rw [terminalCarrierNodeActiveValues_eq_of_matches
    shape (descriptor, descriptor) rfl shapeMatches shapeAxisAligned]
  have occurrencesEq :
      ((shape.segments .first).zipIdx.flatMap fun tagged =>
          neighborTranslations.map fun translate =>
            ((⟨descriptor.edgeIndex, tagged.2,
                tagged.1.evalPair (descriptor, descriptor)⟩ :
              IndexedGridSegment), translate)) =
        descriptor.selfIndexedNeighborOccurrences := by
    have indexedEq := shape.map_evalPair_indexedSegments .first
      (descriptor, descriptor) shapeMatches'
    have indexedEq' :
        ((shape.segments .first).zipIdx.map fun taggedSegment =>
            IndexedGridSegment.mk descriptor.edgeIndex taggedSegment.2
              (taggedSegment.1.evalPair (descriptor, descriptor))) =
          descriptor.indexedSegments descriptor.edgeIndex := by
      simpa [descriptorAt] using indexedEq
    unfold RouteDescriptor.selfIndexedNeighborOccurrences
      RouteDescriptor.neighborOccurrences
    rw [← indexedEq', List.flatMap_map]
  rw [occurrencesEq]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
