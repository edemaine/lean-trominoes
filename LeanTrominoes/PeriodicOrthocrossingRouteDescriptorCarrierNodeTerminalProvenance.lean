/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrenceCarrierTerminalNodeMembership
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorRetainedCarrierBitData

/-! # Terminal provenance in retained route-descriptor node streams -/

namespace LeanTrominoes.PeriodicOrthocrossing

theorem terminal_mem_routeDescriptorRetainedCarrierNodesAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor)
    (terminal : SegmentTerminal)
    (member : CarrierNode.terminal terminal ∈
      routeDescriptorRetainedCarrierNodesAtPeriod period descriptors) :
    ∃ occurrence ∈ routeDescriptorNeighborOccurrences descriptors,
      terminal = ⟨occurrence.1, occurrence.2, .start⟩ ∨
        terminal = ⟨occurrence.1, occurrence.2, .finish⟩ := by
  unfold routeDescriptorRetainedCarrierNodesAtPeriod
    retainedCarrierNodesOfOccurrencesAndPairsAtPeriod at member
  rcases List.mem_append.mp member with terminalMember | boundaryMember
  · rw [mem_flatMap_occurrenceCarrierTerminalNodes_iff]
      at terminalMember
    rcases terminalMember with
      ⟨occurrence, occurrenceMember, startEqual | finishEqual⟩
    · exact ⟨occurrence, occurrenceMember,
        Or.inl (CarrierNode.terminal.inj startEqual)⟩
    · exact ⟨occurrence, occurrenceMember,
        Or.inr (CarrierNode.terminal.inj finishEqual)⟩
  · simp [crossingRecordCarrierBoundaryNodes] at boundaryMember

end LeanTrominoes.PeriodicOrthocrossing
