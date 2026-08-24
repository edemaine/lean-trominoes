/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisShapeSemantics

/-! # Axis semantics of rejected terminal carrier-key shapes -/

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

private theorem Segment.terminalCarrierKeyRejectedActiveDatumBlocks
    (descriptors : List RouteDescriptor) (descriptor : RouteDescriptor)
    (shape : RouteShape) (segment : Segment) (segmentIndex : Nat)
    (guardFalse :
      (shape.guard .first).evalPair (descriptor, descriptor) = false) :
    FixedAxisUnaryFields.ActiveDatumBlocks (value descriptors)
      ((segment.carrierAxisPredicates shape).map fun predicate =>
        predicate.evalTokens
          (descriptorPairTokens (descriptor, descriptor)))
      (segment.terminalCarrierKeyRecipeAxisBlocks segmentIndex)
      (segment.terminalCarrierKeyTemplateBlocks
        (descriptor, descriptor) segmentIndex) := by
  have activations :
      ((segment.carrierAxisPredicates shape).map fun predicate =>
        predicate.evalTokens
          (descriptorPairTokens (descriptor, descriptor))) =
        [false, false] := by
    simp [Segment.carrierAxisPredicates,
      Predicate.evalTokens_descriptorPairTokens, evalPair_all,
      guardFalse]
  rw [activations]
  let block := segment.terminalCarrierKeyTemplateBlock
    (descriptor, descriptor) segmentIndex
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

/-- A route shape whose guard fails has only inactive padded terminal slots,
so its axis values agree with the absent-key datum. -/
theorem RouteShape.terminalCarrierKeyActiveDatumBlocks_of_not_matches
    (descriptors : List RouteDescriptor) (descriptor : RouteDescriptor)
    (shape : RouteShape) (notMatches : ¬shape.Matches descriptor) :
    FixedAxisUnaryFields.ActiveDatumBlocks (value descriptors)
      (shape.carrierSegmentPredicates.map fun predicate =>
        predicate.evalTokens
          (descriptorPairTokens (descriptor, descriptor)))
      shape.terminalCarrierKeyRecipeAxisBlocks
      (shape.terminalCarrierKeyTemplateBlocks
        (descriptor, descriptor)) := by
  have guardFalse :
      (shape.guard .first).evalPair (descriptor, descriptor) = false := by
    rw [shape.evalPair_guard]
    simp [notMatches, descriptorAt]
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
  · intro tagged _taggedMember
    exact tagged.1.terminalCarrierKeyRejectedActiveDatumBlocks
      descriptors descriptor shape tagged.2 guardFalse
  · intro tagged _taggedMember
    simp [Segment.carrierAxisPredicates,
      Segment.terminalCarrierKeyRecipeAxisBlocks]
  · intro tagged _taggedMember
    simp [Segment.carrierAxisPredicates,
      Segment.terminalCarrierKeyTemplateBlocks]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
