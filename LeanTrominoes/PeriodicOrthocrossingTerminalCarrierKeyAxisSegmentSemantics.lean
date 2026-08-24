/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFieldsActiveCandidateBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyAxisDatum
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentSelectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorSelfIndexedNeighborOccurrences
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisValueData

/-! # Axis semantics of one terminal carrier-key segment -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open RouteDescriptorCarrierKeyAxisDatum
open RouteDescriptorPairFieldTags

private theorem forall₂_replicate_left
    {First Second : Type*} {Relation : First → Second → Prop}
    (first : First) (seconds : List Second)
    (all : ∀ second ∈ seconds, Relation first second) :
    List.Forall₂ Relation
      (List.replicate seconds.length first) seconds := by
  induction seconds with
  | nil => exact List.Forall₂.nil
  | cons second seconds induction =>
      simp only [List.length_cons, List.replicate_succ]
      exact List.Forall₂.cons
        (all second (by simp))
        (induction (fun item member => all item (by simp [member])))

private theorem terminalTemplateBlock_datum
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (descriptor : RouteDescriptor) (descriptorMember : descriptor ∈ descriptors)
    (segment : Segment) (segmentIndex : Nat)
    (indexedMember :
      (⟨descriptor.edgeIndex, segmentIndex,
          segment.evalPair (descriptor, descriptor)⟩ : IndexedGridSegment) ∈
        descriptor.indexedSegments descriptor.edgeIndex)
    (template : Template (Nat × Nat × Cell))
    (templateMember : template ∈
      segment.terminalCarrierKeyTemplateBlock
        (descriptor, descriptor) segmentIndex) :
    value descriptors (some template.value) =
      FixedAxisUnaryFields.value true
        (decide (segment.evalPair
          (descriptor, descriptor)).IsHorizontal) := by
  unfold Segment.terminalCarrierKeyTemplateBlock at templateMember
  rcases List.mem_flatMap.mp templateMember with
    ⟨translate, translateMember, templateMember⟩
  have templateEq : template =
      (⟨(descriptor.edgeIndex, segmentIndex, translate), true⟩ :
        Template (Nat × Nat × Cell)) := by
    simpa using templateMember
  subst template
  let indexed : IndexedGridSegment :=
    ⟨descriptor.edgeIndex, segmentIndex,
      segment.evalPair (descriptor, descriptor)⟩
  have localMember :
      (indexed, translate) ∈
        descriptor.neighborOccurrences descriptor.edgeIndex := by
    unfold RouteDescriptor.neighborOccurrences
    rw [List.mem_flatMap]
    exact ⟨indexed, indexedMember,
      List.mem_map.mpr ⟨translate, translateMember, rfl⟩⟩
  have globalMember :
      (indexed, translate) ∈
        routeDescriptorNeighborOccurrences descriptors := by
    rw [routeDescriptorNeighborOccurrences_eq_selfIndexedFlatMap
      descriptors selfIndexed]
    rw [List.mem_flatMap]
    exact ⟨descriptor, descriptorMember, localMember⟩
  simpa [occurrenceKey, PeriodicGridDrawing.SegmentOccurrenceKey,
    indexed] using
    value_some_occurrenceKey descriptors (indexed, translate) globalMember

/-- On one selected diagonal axis-aligned segment, the two predicate,
axis, and terminal-template blocks satisfy the key-derived datum relation. -/
theorem Segment.terminalCarrierKeyActiveDatumBlocks
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (descriptor : RouteDescriptor) (descriptorMember : descriptor ∈ descriptors)
    (shape : RouteShape) (segment : Segment) (segmentIndex : Nat)
    (shapeMatches : shape.Matches descriptor)
    (axisAligned :
      (segment.evalPair (descriptor, descriptor)).IsAxisAligned)
    (indexedMember :
      (⟨descriptor.edgeIndex, segmentIndex,
          segment.evalPair (descriptor, descriptor)⟩ : IndexedGridSegment) ∈
        descriptor.indexedSegments descriptor.edgeIndex) :
    FixedAxisUnaryFields.ActiveDatumBlocks (value descriptors)
      ((segment.carrierAxisPredicates shape).map fun predicate =>
        predicate.evalTokens
          (descriptorPairTokens (descriptor, descriptor)))
      (segment.terminalCarrierKeyRecipeAxisBlocks segmentIndex)
      (segment.terminalCarrierKeyTemplateBlocks
        (descriptor, descriptor) segmentIndex) := by
  have shapeMatches' :
      shape.Matches (descriptorAt (descriptor, descriptor) .first) := by
    simpa [descriptorAt] using shapeMatches
  let block := segment.terminalCarrierKeyTemplateBlock
    (descriptor, descriptor) segmentIndex
  have blockLength :
      (segment.terminalCarrierKeyRecipeBlock segmentIndex).length =
        block.length := by
    simp [block, Segment.terminalCarrierKeyRecipeBlock,
      Segment.terminalCarrierKeyTemplateBlock]
  rcases axisAligned with horizontal | vertical
  · have notVertical :
        ¬(segment.evalPair (descriptor, descriptor)).IsVertical := by
      intro isVertical
      exact horizontal.2 isVertical.1
    have activations :
        ((segment.carrierAxisPredicates shape).map fun predicate =>
          predicate.evalTokens
            (descriptorPairTokens (descriptor, descriptor))) =
          [true, false] := by
      simp [Segment.carrierAxisPredicates,
        Predicate.evalTokens_descriptorPairTokens,
        RouteShape.evalPair_guard, shapeMatches', horizontal, notVertical]
    rw [activations]
    unfold Segment.terminalCarrierKeyRecipeAxisBlocks
      Segment.terminalCarrierKeyTemplateBlocks
    rw [blockLength]
    refine ⟨?_, ⟨?_, trivial⟩⟩
    · apply forall₂_replicate_left
      intro template templateMember
      have datumEq := terminalTemplateBlock_datum
        descriptors selfIndexed descriptor descriptorMember
        segment segmentIndex indexedMember template templateMember
      simpa [FixedAxisUnaryFields.value,
        Template.activate, horizontal] using datumEq.symm
    · apply forall₂_replicate_left
      intro template _templateMember
      simp [FixedAxisUnaryFields.value, Template.activate,
        RouteDescriptorCarrierKeyAxisDatum.value_none]
  · have notHorizontal :
        ¬(segment.evalPair (descriptor, descriptor)).IsHorizontal := by
      intro isHorizontal
      exact vertical.2 isHorizontal.1
    have activations :
        ((segment.carrierAxisPredicates shape).map fun predicate =>
          predicate.evalTokens
            (descriptorPairTokens (descriptor, descriptor))) =
          [false, true] := by
      simp [Segment.carrierAxisPredicates,
        Predicate.evalTokens_descriptorPairTokens,
        RouteShape.evalPair_guard, shapeMatches', vertical, notHorizontal]
    rw [activations]
    unfold Segment.terminalCarrierKeyRecipeAxisBlocks
      Segment.terminalCarrierKeyTemplateBlocks
    rw [blockLength]
    refine ⟨?_, ⟨?_, trivial⟩⟩
    · apply forall₂_replicate_left
      intro template _templateMember
      simp [FixedAxisUnaryFields.value, Template.activate,
        RouteDescriptorCarrierKeyAxisDatum.value_none]
    · apply forall₂_replicate_left
      intro template templateMember
      have datumEq := terminalTemplateBlock_datum
        descriptors selfIndexed descriptor descriptorMember
        segment segmentIndex indexedMember template templateMember
      simpa [FixedAxisUnaryFields.value,
        Template.activate, notHorizontal] using datumEq.symm

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
