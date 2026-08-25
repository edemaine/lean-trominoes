/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftCandidateFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftCrossingCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftTerminalCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData

/-! # Complete ownership-shift fields aligned with carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOwnershipShiftCandidateFieldStream

open CarrierOwnershipShiftField
open PaddedSupportedLastRepresentativeEqualityRows

/-- Active terminal and crossing slots carry their exact ownership shift at
the common drawing period. -/
theorem values_forall₂_paddedCarrierNodeCandidateStream
    (field : Field) (period : Nat)
    (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors,
      descriptor.gridSize = period) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field period node)
      (paddedCarrierNodeCandidateStream descriptors)
      (values field descriptors) := by
  unfold paddedCarrierNodeCandidateStream values terminalValues
    crossingValues
  exact List.Forall₂.append
    (RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream_ownershipShift_forall₂
      field period descriptors)
    (RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream_ownershipShift_forall₂
      field period descriptors periodEq)

end CarrierOwnershipShiftCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing
