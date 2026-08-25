/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCrossingFieldAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderTerminalStreamFieldAlignmentSemantics

/-! # Complete carrier order fields aligned with semantic nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderCandidateFieldStream

open PaddedSupportedLastRepresentativeEqualityRows

/-- Terminal and crossing candidate fields agree with every active semantic
node column; inactive padding may carry arbitrary affine values. -/
theorem values_forall₂_carrierOrderCandidateNodeStream
    (keepPositive : Bool) (period : Nat)
    (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors,
      descriptor.gridSize = period) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = carrierNodeOrderFieldAtPeriod keepPositive period node)
      (carrierOrderCandidateNodeStream descriptors)
      (values keepPositive descriptors) := by
  unfold carrierOrderCandidateNodeStream values
  exact List.Forall₂.append
    (RouteDescriptorPairAffine.terminalDirectionalCarrierNodeCandidateStream_forall₂
      keepPositive period descriptors periodEq)
    (RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream_forall₂
      keepPositive period descriptors periodEq)

end CarrierOrderCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing
