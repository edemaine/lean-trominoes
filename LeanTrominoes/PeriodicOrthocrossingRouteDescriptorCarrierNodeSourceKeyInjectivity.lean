/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyConstructorSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyRetainedBoundarySemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyTerminalSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeBoundaryProvenance
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeTerminalProvenance

/-! # Source-key injectivity on retained route-descriptor carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing

open CarrierNodeSourceKeys

/-- On the exact retained node stream reconstructed from route descriptors,
the compact two-key source representation is injective. -/
theorem sourceKeyPair_injectiveOn_routeDescriptorRetainedCarrierNodesAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    ∀ first ∈ routeDescriptorRetainedCarrierNodesAtPeriod
        period descriptors,
      ∀ second ∈ routeDescriptorRetainedCarrierNodesAtPeriod
          period descriptors,
        pair first = pair second → first = second := by
  intro first firstMember second secondMember equal
  cases first with
  | terminal firstTerminal =>
      cases second with
      | terminal secondTerminal =>
          have firstData :=
            terminal_mem_routeDescriptorRetainedCarrierNodesAtPeriod
              period descriptors firstTerminal firstMember
          have secondData :=
            terminal_mem_routeDescriptorRetainedCarrierNodesAtPeriod
              period descriptors secondTerminal secondMember
          rcases firstData with
            ⟨firstOccurrence, firstOccurrenceMember,
              firstStart | firstFinish⟩ <;>
            rcases secondData with
              ⟨secondOccurrence, secondOccurrenceMember,
                secondStart | secondFinish⟩
          all_goals
            subst firstTerminal
            subst secondTerminal
            exact terminal_eq_of_sourceKeyPair_eq descriptors
              firstOccurrence secondOccurrence
              firstOccurrenceMember secondOccurrenceMember _ _ equal
      | boundary secondBoundary =>
          exact False.elim
            (terminal_sourceKeyPair_ne_boundary
              firstTerminal secondBoundary equal)
  | boundary firstBoundary =>
      cases second with
      | terminal secondTerminal =>
          exact False.elim
            (terminal_sourceKeyPair_ne_boundary
              secondTerminal firstBoundary equal.symm)
      | boundary secondBoundary =>
          rcases
              boundary_mem_routeDescriptorRetainedCarrierNodesAtPeriod
                period descriptors firstBoundary firstMember with
            ⟨firstPair, firstPairMember, firstShift, _firstShiftMember,
              firstSide, firstBoundaryEqual⟩
          rcases
              boundary_mem_routeDescriptorRetainedCarrierNodesAtPeriod
                period descriptors secondBoundary secondMember with
            ⟨secondPair, secondPairMember, secondShift, _secondShiftMember,
              secondSide, secondBoundaryEqual⟩
          subst firstBoundary
          subst secondBoundary
          have firstPairMembers := List.mem_product.mp
            (List.mem_filter.mp firstPairMember).1
          have secondPairMembers := List.mem_product.mp
            (List.mem_filter.mp secondPairMember).1
          exact retainedBoundary_eq_of_sourceKeyPair_eq
            descriptors period firstPair secondPair
            firstPairMembers.1 firstPairMembers.2
            secondPairMembers.1 secondPairMembers.2
            firstShift secondShift firstSide secondSide equal

end LeanTrominoes.PeriodicOrthocrossing
