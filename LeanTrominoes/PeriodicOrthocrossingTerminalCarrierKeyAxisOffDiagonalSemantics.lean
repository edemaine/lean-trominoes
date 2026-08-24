/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentPredicateSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisDiagonalSemantics

/-! # Axis semantics of off-diagonal terminal carrier-key scans -/

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

private theorem Segment.terminalCarrierKeyOffDiagonalActiveDatumBlocks
    (descriptors : List RouteDescriptor)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex)
    (shape : RouteShape) (segment : Segment) (segmentIndex : Nat) :
    FixedAxisUnaryFields.ActiveDatumBlocks (value descriptors)
      ((segment.carrierAxisPredicates shape).map fun predicate =>
        predicate.evalTokens (descriptorPairTokens pair))
      (segment.terminalCarrierKeyRecipeAxisBlocks segmentIndex)
      (segment.terminalCarrierKeyTemplateBlocks pair segmentIndex) := by
  have diagonalFalse :
      carrierSegmentSameEdgeIndex.evalPair pair = false := by
    simp [edgeIndexNe]
  have activations :
      ((segment.carrierAxisPredicates shape).map fun predicate =>
        predicate.evalTokens (descriptorPairTokens pair)) =
        [false, false] := by
    simp [Segment.carrierAxisPredicates,
      Predicate.evalTokens_descriptorPairTokens, evalPair_all,
      diagonalFalse]
  rw [activations]
  let block := segment.terminalCarrierKeyTemplateBlock pair segmentIndex
  have blockLength :
      (segment.terminalCarrierKeyRecipeBlock segmentIndex).length =
        block.length := by
    simp [block, Segment.terminalCarrierKeyRecipeBlock,
      Segment.terminalCarrierKeyTemplateBlock]
  unfold Segment.terminalCarrierKeyRecipeAxisBlocks
    Segment.terminalCarrierKeyTemplateBlocks
  rw [blockLength]
  refine ⟨?_, ⟨?_, trivial⟩⟩ <;>
    apply forall₂_replicate_left <;>
    intro template _templateMember <;>
    simp [FixedAxisUnaryFields.value, Template.activate,
      RouteDescriptorCarrierKeyAxisDatum.value_none]

private theorem RouteShape.terminalCarrierKeyOffDiagonalActiveDatumBlocks
    (descriptors : List RouteDescriptor)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex)
    (shape : RouteShape) :
    FixedAxisUnaryFields.ActiveDatumBlocks (value descriptors)
      (shape.carrierSegmentPredicates.map fun predicate =>
        predicate.evalTokens (descriptorPairTokens pair))
      shape.terminalCarrierKeyRecipeAxisBlocks
      (shape.terminalCarrierKeyTemplateBlocks pair) := by
  have activationsEq :
      (shape.carrierSegmentPredicates.map fun predicate =>
        predicate.evalTokens (descriptorPairTokens pair)) =
      (shape.segments .first).zipIdx.flatMap fun tagged =>
        (tagged.1.carrierAxisPredicates shape).map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair) := by
    unfold RouteShape.carrierSegmentPredicates
    rw [List.map_flatMap]
    conv_lhs =>
      rw [← List.zipIdx_map_fst 0 (shape.segments .first),
        List.flatMap_map]
  rw [activationsEq]
  unfold RouteShape.terminalCarrierKeyRecipeAxisBlocks
    RouteShape.terminalCarrierKeyTemplateBlocks
  apply FixedAxisUnaryFields.ActiveDatumBlocks.flatMap
  · intro tagged _taggedMember
    exact tagged.1.terminalCarrierKeyOffDiagonalActiveDatumBlocks
      descriptors pair edgeIndexNe shape tagged.2
  · intro tagged _taggedMember
    simp [Segment.carrierAxisPredicates,
      Segment.terminalCarrierKeyRecipeAxisBlocks]
  · intro tagged _taggedMember
    simp [Segment.carrierAxisPredicates,
      Segment.terminalCarrierKeyTemplateBlocks]

/-- Unequal stored edge indices make the complete terminal scan key-derived
through its uniformly inactive padded slots. -/
theorem terminalCarrierKeyActiveDatumBlocks_of_edgeIndex_ne
    (descriptors : List RouteDescriptor)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    FixedAxisUnaryFields.ActiveDatumBlocks (value descriptors)
      (terminalCarrierKeyActivations (descriptorPairTokens pair))
      terminalCarrierKeyRecipeAxisBlocks
      (terminalCarrierKeyTemplateBlocks pair) := by
  unfold terminalCarrierKeyActivations carrierSegmentPredicates
    terminalCarrierKeyRecipeAxisBlocks terminalCarrierKeyTemplateBlocks
  rw [List.map_flatMap]
  apply FixedAxisUnaryFields.ActiveDatumBlocks.flatMap
  · intro shape _shapeMember
    exact shape.terminalCarrierKeyOffDiagonalActiveDatumBlocks
      descriptors pair edgeIndexNe
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
