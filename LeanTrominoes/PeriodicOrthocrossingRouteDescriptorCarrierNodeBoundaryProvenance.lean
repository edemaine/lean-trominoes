/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingRecordCarrierBoundaryNodeMembership
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCrossingRecordMembership
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorRetainedCarrierBitData

/-! # Boundary provenance in retained route-descriptor node streams -/

namespace LeanTrominoes.PeriodicOrthocrossing

theorem boundary_mem_routeDescriptorRetainedCarrierNodesAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor)
    (boundary : CrossingBoundary)
    (member : CarrierNode.boundary boundary ∈
      routeDescriptorRetainedCarrierNodesAtPeriod period descriptors) :
    ∃ pair ∈
        routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
          period descriptors,
      ∃ shift ∈ carrierCrossingRetentionShifts,
        ∃ side : CrossingSide,
          boundary =
            ⟨crossingRecordPeriodTranslateAtPeriod period
                (occurrencePairCrossingRecordAtPeriod period pair) shift,
              side⟩ := by
  unfold routeDescriptorRetainedCarrierNodesAtPeriod
    retainedCarrierNodesOfOccurrencesAndPairsAtPeriod at member
  rcases List.mem_append.mp member with terminalMember | boundaryMember
  · simp [occurrenceCarrierTerminalNodes, occurrenceTerminals]
      at terminalMember
  · rw [mem_flatMap_crossingRecordCarrierBoundaryNodes_iff]
      at boundaryMember
    rcases boundaryMember with
      ⟨record, recordMember,
        leftEqual | rightEqual | topEqual | bottomEqual⟩
    all_goals
      rw [mem_occurrencePairRetainedCrossingRecordScanAtPeriod_iff]
        at recordMember
      rcases recordMember with
        ⟨pair, pairMember, shift, shiftMember, recordEqual⟩
    · exact ⟨pair, pairMember, shift, shiftMember, .left,
        (CarrierNode.boundary.inj leftEqual).trans
          (congrArg (fun record : CrossingRecord =>
            (⟨record, CrossingSide.left⟩ : CrossingBoundary))
            recordEqual.symm)⟩
    · exact ⟨pair, pairMember, shift, shiftMember, .right,
        (CarrierNode.boundary.inj rightEqual).trans
          (congrArg (fun record : CrossingRecord =>
            (⟨record, CrossingSide.right⟩ : CrossingBoundary))
            recordEqual.symm)⟩
    · exact ⟨pair, pairMember, shift, shiftMember, .top,
        (CarrierNode.boundary.inj topEqual).trans
          (congrArg (fun record : CrossingRecord =>
            (⟨record, CrossingSide.top⟩ : CrossingBoundary))
            recordEqual.symm)⟩
    · exact ⟨pair, pairMember, shift, shiftMember, .bottom,
        (CarrierNode.boundary.inj bottomEqual).trans
          (congrArg (fun record : CrossingRecord =>
            (⟨record, CrossingSide.bottom⟩ : CrossingBoundary))
            recordEqual.symm)⟩

end LeanTrominoes.PeriodicOrthocrossing
