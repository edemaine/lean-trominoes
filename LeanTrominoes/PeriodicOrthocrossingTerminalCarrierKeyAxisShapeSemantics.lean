/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisSegmentSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairOccurrenceTemplateSemantics

/-! # Axis semantics of one selected terminal carrier-key shape -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorCarrierKeyAxisDatum
open RouteDescriptorPairFieldTags

/-- A matching route shape's complete terminal predicate/axis/template family
is key-derived on a diagonal descriptor pair. -/
theorem RouteShape.terminalCarrierKeyActiveDatumBlocks_diagonal
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (descriptor : RouteDescriptor) (descriptorMember : descriptor ∈ descriptors)
    (shape : RouteShape) (shapeMatches : shape.Matches descriptor)
    (axisAligned : ∀ segment ∈ shape.segments .first,
      (segment.evalPair (descriptor, descriptor)).IsAxisAligned) :
    FixedAxisUnaryFields.ActiveDatumBlocks (value descriptors)
      (shape.carrierSegmentPredicates.map fun predicate =>
        predicate.evalTokens
          (descriptorPairTokens (descriptor, descriptor)))
      shape.terminalCarrierKeyRecipeAxisBlocks
      (shape.terminalCarrierKeyTemplateBlocks
        (descriptor, descriptor)) := by
  have shapeMatches' :
      shape.Matches (descriptorAt (descriptor, descriptor) .first) := by
    simpa [descriptorAt] using shapeMatches
  have indexedEq := shape.map_evalPair_indexedSegments .first
    (descriptor, descriptor) shapeMatches'
  have indexedEq' :
      ((shape.segments .first).zipIdx.map fun tagged =>
        (⟨descriptor.edgeIndex, tagged.2,
          tagged.1.evalPair (descriptor, descriptor)⟩ :
            IndexedGridSegment)) =
        descriptor.indexedSegments descriptor.edgeIndex := by
    simpa [descriptorAt] using indexedEq
  have activationsEq :
      (shape.carrierSegmentPredicates.map fun predicate =>
        predicate.evalTokens
          (descriptorPairTokens (descriptor, descriptor))) =
      (shape.segments .first).zipIdx.flatMap fun tagged =>
        (tagged.1.carrierAxisPredicates shape).map fun predicate =>
          predicate.evalTokens
            (descriptorPairTokens (descriptor, descriptor)) := by
    unfold RouteShape.carrierSegmentPredicates
    rw [List.map_flatMap]
    conv_lhs =>
      rw [← List.zipIdx_map_fst 0 (shape.segments .first),
        List.flatMap_map]
  rw [activationsEq]
  unfold RouteShape.terminalCarrierKeyRecipeAxisBlocks
    RouteShape.terminalCarrierKeyTemplateBlocks
  apply FixedAxisUnaryFields.ActiveDatumBlocks.flatMap
  · intro tagged taggedMember
    apply tagged.1.terminalCarrierKeyActiveDatumBlocks
      descriptors selfIndexed descriptor descriptorMember shape
      tagged.2 shapeMatches (axisAligned tagged.1
        (List.fst_mem_of_mem_zipIdx taggedMember))
    rw [← indexedEq']
    exact List.mem_map.mpr ⟨tagged, taggedMember, rfl⟩
  · intro tagged _taggedMember
    simp [Segment.carrierAxisPredicates,
      Segment.terminalCarrierKeyRecipeAxisBlocks]
  · intro tagged _taggedMember
    simp [Segment.carrierAxisPredicates,
      Segment.terminalCarrierKeyTemplateBlocks]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
