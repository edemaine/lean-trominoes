/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingTranslationDegree
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLinks

/-! # Neighboring occurrence keys of retained carrier representatives -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- The common carrier key of every selected retained link has one of the
neighboring translations used by the finite source window. -/
theorem retainedDrawingCompleteCarrierLink_key_translate_neighbor
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {link : EqualityLink CarrierNode}
    (linkMember : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    IsNeighborTranslation link.first.carrierKey.2.2 := by
  have selected :=
    (mem_retainedDrawingCompleteCarrierLinks_iff graph link).mp linkMember
  have endpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph linkMember
  have common :=
    retainedDrawingCompleteCarrierLinks_common_key graph linkMember
  cases firstEq : link.first with
  | boundary firstBoundary =>
      have firstBoundaryMember :
          firstBoundary ∈ retainedCrossingBoundaries graph := by
        rw [firstEq] at endpoints
        unfold retainedDrawingCarrierNodes at endpoints
        simpa using endpoints.1
      have shiftZero :
          crossingPeriodShift graph firstBoundary.crossing = (0, 0) := by
        simpa [CarrierLinkIsRepresentative,
          carrierLinkRepresentativeShift, firstEq] using selected.2
      have normalizedMember :=
        retainedCrossingBoundary_periodNormalize_mem
          graph firstBoundaryMember
      rw [CrossingBoundary.periodNormalize_eq_self_of_shift_eq_zero
        graph firstBoundary shiftZero] at normalizedMember
      simpa [CarrierNode.carrierKey,
        CrossingBoundary.carrierKey_eq_indexed_translate,
        PeriodicGridDrawing.SegmentOccurrenceKey] using
        (drawingCrossingBoundary_indexed_mem_and_translate_neighbor
          graph normalizedMember).2
  | terminal firstTerminal =>
      cases secondEq : link.second with
      | boundary secondBoundary =>
          have secondBoundaryMember :
              secondBoundary ∈ retainedCrossingBoundaries graph := by
            rw [secondEq] at endpoints
            unfold retainedDrawingCarrierNodes at endpoints
            simpa using endpoints.2
          have shiftZero :
              crossingPeriodShift graph secondBoundary.crossing =
                (0, 0) := by
            simpa [CarrierLinkIsRepresentative,
              carrierLinkRepresentativeShift, firstEq, secondEq] using
              selected.2
          have normalizedMember :=
            retainedCrossingBoundary_periodNormalize_mem
              graph secondBoundaryMember
          rw [CrossingBoundary.periodNormalize_eq_self_of_shift_eq_zero
            graph secondBoundary shiftZero] at normalizedMember
          have secondNeighbor :=
            (drawingCrossingBoundary_indexed_mem_and_translate_neighbor
              graph normalizedMember).2
          have translateEq :
              firstTerminal.translate = secondBoundary.translate := by
            have keyEq :=
              congrArg (fun key : Nat × Nat × Cell => key.2.2) common
            rw [firstEq, secondEq] at keyEq
            simpa [CarrierNode.carrierKey,
              SegmentTerminal.carrierKey,
              CrossingBoundary.carrierKey_eq_indexed_translate,
              PeriodicGridDrawing.SegmentOccurrenceKey] using keyEq
          simpa [CarrierNode.carrierKey,
            SegmentTerminal.carrierKey,
            PeriodicGridDrawing.SegmentOccurrenceKey,
            translateEq] using secondNeighbor
      | terminal secondTerminal =>
          have translateZero :=
            carrierLinkRepresentative_terminal_terminal_translate_eq_zero
              graph firstEq secondEq selected.2
          simp [CarrierNode.carrierKey,
            SegmentTerminal.carrierKey,
            PeriodicGridDrawing.SegmentOccurrenceKey,
            translateZero, IsNeighborTranslation]

end LeanTrominoes.PeriodicOrthocrossing
