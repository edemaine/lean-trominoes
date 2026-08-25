/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockActivity
import LeanTrominoes.PaddedSupportedCandidateBlockAppend
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateNodeStreamData
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalAlternativeAlignment
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalRecipeSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentPredicateSemantics

/-! # Activity semantics of carrier order-coordinate node candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairFieldTags

/-- Splitting one axis predicate into its decreasing and increasing cases
does not alter the compact active terminal-node block. -/
theorem Segment.terminalDirectionalActiveValues_eq_axisActiveValues
    (segment : Segment) (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor) (segmentIndex : Nat) :
    activeValues
        ((segment.terminalDirectionalPredicates shape).map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (segment.terminalDirectionalCarrierNodeTemplateBlocks
          pair segmentIndex) =
      activeValues
        ((segment.carrierAxisPredicates shape).map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (segment.terminalCarrierNodeTemplateBlocks pair segmentIndex) := by
  simp only [Segment.terminalDirectionalPredicates,
    Segment.terminalDirectionalCarrierNodeTemplateBlocks,
    Segment.carrierAxisPredicates,
    Segment.terminalCarrierNodeTemplateBlocks,
    List.map_cons, List.map_nil, activeValues]
  simp only [Predicate.evalTokens_descriptorPairTokens,
    Predicate.evalPair_conjunction, Predicate.evalPair_negation]
  cases (all [carrierSegmentSameEdgeIndex, shape.guard .first,
    segment.carrierIsHorizontal]).evalPair pair <;>
    cases (segment.increasingPredicate true).evalPair pair <;>
      cases (all [carrierSegmentSameEdgeIndex, shape.guard .first,
        segment.carrierIsVertical]).evalPair pair <;>
        cases (segment.increasingPredicate false).evalPair pair <;> rfl

theorem RouteShape.terminalDirectionalActiveValues_eq_axisActiveValues
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor) :
    activeValues
        (shape.terminalDirectionalPredicates.map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (shape.terminalDirectionalCarrierNodeTemplateBlocks pair) =
      activeValues
        (shape.carrierSegmentPredicates.map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (shape.terminalCarrierNodeTemplateBlocks pair) := by
  unfold RouteShape.terminalDirectionalPredicates
    RouteShape.terminalDirectionalCarrierNodeTemplateBlocks
    RouteShape.carrierSegmentPredicates
    RouteShape.terminalCarrierNodeTemplateBlocks
  rw [List.map_flatMap, List.map_flatMap]
  have aligned : ∀ (segments : List Segment) (start : Nat),
      activeValues
          (segments.flatMap fun segment =>
            (segment.terminalDirectionalPredicates shape).map fun predicate =>
              predicate.evalTokens (descriptorPairTokens pair))
          ((segments.zipIdx start).flatMap fun tagged =>
            tagged.1.terminalDirectionalCarrierNodeTemplateBlocks
              pair tagged.2) =
        activeValues
          (segments.flatMap fun segment =>
            (segment.carrierAxisPredicates shape).map fun predicate =>
              predicate.evalTokens (descriptorPairTokens pair))
          ((segments.zipIdx start).flatMap fun tagged =>
            tagged.1.terminalCarrierNodeTemplateBlocks pair tagged.2) := by
    intro segments start
    induction segments generalizing start with
    | nil => rfl
    | cons segment segments induction =>
        simp only [List.flatMap_cons, List.zipIdx_cons]
        rw [activeValues_append, activeValues_append]
        · rw [segment.terminalDirectionalActiveValues_eq_axisActiveValues,
            induction]
        · rfl
        · rfl
  exact aligned (shape.segments .first) 0

theorem terminalDirectionalActiveValues_eq_terminalActiveValues
    (pair : RouteDescriptor × RouteDescriptor) :
    activeValues
        (terminalDirectionalPredicates.map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (terminalDirectionalCarrierNodeTemplateBlocks pair) =
      activeValues
        (terminalCarrierKeyActivations (descriptorPairTokens pair))
        (terminalCarrierNodeTemplateBlocks pair) := by
  unfold terminalDirectionalPredicates
    terminalDirectionalCarrierNodeTemplateBlocks
    terminalCarrierKeyActivations carrierSegmentPredicates
    terminalCarrierNodeTemplateBlocks
  rw [List.map_flatMap, List.map_flatMap]
  rw [activeValues_flatMap, activeValues_flatMap]
  · apply List.flatMap_congr
    intro shape _shapeMember
    exact shape.terminalDirectionalActiveValues_eq_axisActiveValues pair
  · intro shape _shapeMember
    simp [RouteShape.carrierSegmentPredicates,
      RouteShape.terminalCarrierNodeTemplateBlocks,
      Segment.carrierAxisPredicates,
      Segment.terminalCarrierNodeTemplateBlocks]
  · intro shape _shapeMember
    simp [RouteShape.terminalDirectionalPredicates,
      RouteShape.terminalDirectionalCarrierNodeTemplateBlocks,
      Segment.terminalDirectionalCarrierNodeTemplateBlocks]

theorem filterMap_terminalDirectionalCarrierNodeCandidates
    (pair : RouteDescriptor × RouteDescriptor) :
    (terminalDirectionalCarrierNodeCandidates pair).filterMap
        Candidate.value =
      (paddedTerminalCarrierNodeCandidates pair).filterMap
        Candidate.value := by
  unfold terminalDirectionalCarrierNodeCandidates
    paddedTerminalCarrierNodeCandidates
  rw [filterMap_value_candidates, filterMap_value_candidates]
  exact terminalDirectionalActiveValues_eq_terminalActiveValues pair

theorem filterMap_terminalDirectionalCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    (terminalDirectionalCarrierNodeCandidateStream descriptors).filterMap
        Candidate.value =
      (paddedTerminalCarrierNodeCandidateStream descriptors).filterMap
        Candidate.value := by
  unfold terminalDirectionalCarrierNodeCandidateStream
    paddedTerminalCarrierNodeCandidateStream
  induction descriptors ×ˢ descriptors with
  | nil => rfl
  | cons pair pairs induction =>
      rw [List.flatMap_cons, List.flatMap_cons,
        List.filterMap_append, List.filterMap_append,
        filterMap_terminalDirectionalCarrierNodeCandidates, induction]

end RouteDescriptorPairAffine

/-- Direction splitting only inserts inactive padding: compacting the full
order-candidate node stream recovers the established carrier-node stream. -/
theorem filterMap_carrierOrderCandidateNodeStream
    (descriptors : List RouteDescriptor) :
    (carrierOrderCandidateNodeStream descriptors).filterMap
        PaddedSupportedLastRepresentativeEqualityRows.Candidate.value =
      (paddedCarrierNodeCandidateStream descriptors).filterMap
        PaddedSupportedLastRepresentativeEqualityRows.Candidate.value := by
  unfold carrierOrderCandidateNodeStream paddedCarrierNodeCandidateStream
  rw [List.filterMap_append, List.filterMap_append,
    RouteDescriptorPairAffine.filterMap_terminalDirectionalCarrierNodeCandidateStream]

end LeanTrominoes.PeriodicOrthocrossing
