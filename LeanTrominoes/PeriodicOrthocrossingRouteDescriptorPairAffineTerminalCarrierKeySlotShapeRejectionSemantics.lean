/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockAppend
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentSelectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotData

/-! # Rejected route-shape terminal carrier-key slots -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- A route shape whose guard fails has no active terminal-key values. -/
theorem RouteShape.terminalCarrierKeyActiveValues_eq_nil_of_not_matches
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor)
    (notMatches : ¬shape.Matches pair.1) :
    activeValues
        (shape.carrierSegmentPredicates.map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (shape.terminalCarrierKeyTemplateBlocks pair) = [] := by
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
  unfold RouteShape.terminalCarrierKeyTemplateBlocks
  rw [activeValues_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro tagged _taggedMember
    have guardFalse : (shape.guard .first).evalPair pair = false := by
      rw [shape.evalPair_guard]
      simp [notMatches, descriptorAt]
    simp [Segment.carrierAxisPredicates,
      Segment.terminalCarrierKeyTemplateBlocks,
      Predicate.evalTokens_descriptorPairTokens, evalPair_all,
      guardFalse, activeValues]
  · intro tagged _taggedMember
    simp [Segment.carrierAxisPredicates,
      Segment.terminalCarrierKeyTemplateBlocks]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
