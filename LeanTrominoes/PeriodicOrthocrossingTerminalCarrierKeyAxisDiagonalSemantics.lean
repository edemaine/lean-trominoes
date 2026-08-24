/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisRejectedShapeSemantics

/-! # Axis semantics of one diagonal terminal carrier-key scan -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorCarrierKeyAxisDatum
open RouteDescriptorPairFieldTags

/-- The complete fixed terminal scan of one diagonal descriptor is a
key-derived padded axis stream. -/
theorem terminalCarrierKeyActiveDatumBlocks_diagonal
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (descriptor : RouteDescriptor) (descriptorMember : descriptor ∈ descriptors)
    (axisAligned : ∀ segment ∈ gridPolylineSegments descriptor.route,
      segment.IsAxisAligned) :
    FixedAxisUnaryFields.ActiveDatumBlocks (value descriptors)
      (terminalCarrierKeyActivations
        (descriptorPairTokens (descriptor, descriptor)))
      terminalCarrierKeyRecipeAxisBlocks
      (terminalCarrierKeyTemplateBlocks (descriptor, descriptor)) := by
  unfold terminalCarrierKeyActivations carrierSegmentPredicates
    terminalCarrierKeyRecipeAxisBlocks terminalCarrierKeyTemplateBlocks
  rw [List.map_flatMap]
  apply FixedAxisUnaryFields.ActiveDatumBlocks.flatMap
  · intro shape _shapeMember
    by_cases shapeMatches : shape.Matches descriptor
    · have shapeMatches' :
          shape.Matches (descriptorAt
            (descriptor, descriptor) .first) := by
        simpa [descriptorAt] using shapeMatches
      have segmentsEq := shape.map_evalPair_segments .first
        (descriptor, descriptor) shapeMatches'
      have segmentsEq' :
          (shape.segments .first).map
              (fun segment => segment.evalPair
                (descriptor, descriptor)) =
            gridPolylineSegments descriptor.route := by
        simpa [descriptorAt] using segmentsEq
      have shapeAxisAligned :
          ∀ segment ∈ shape.segments .first,
            (segment.evalPair
              (descriptor, descriptor)).IsAxisAligned := by
        intro segment segmentMember
        apply axisAligned
        rw [← segmentsEq']
        exact List.mem_map_of_mem segmentMember
      exact shape.terminalCarrierKeyActiveDatumBlocks_diagonal
        descriptors selfIndexed descriptor descriptorMember
        shapeMatches shapeAxisAligned
    · exact shape.terminalCarrierKeyActiveDatumBlocks_of_not_matches
        descriptors descriptor shapeMatches
  · intro shape _shapeMember
    simp [RouteShape.carrierSegmentPredicates,
      RouteShape.terminalCarrierKeyRecipeAxisBlocks,
      Segment.carrierAxisPredicates,
      Segment.terminalCarrierKeyRecipeAxisBlocks]
  · intro shape _shapeMember
    simp [RouteShape.carrierSegmentPredicates,
      RouteShape.terminalCarrierKeyTemplateBlocks,
      Segment.carrierAxisPredicates,
      Segment.terminalCarrierKeyTemplateBlocks]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
