/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetCandidateFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetCrossingCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetTerminalCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData

/-! # Complete normalization-offset fields aligned with carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizationOffsetCandidateFieldStream

open CarrierNormalizationOffsetField
open PaddedSupportedLastRepresentativeEqualityRows

/-- Active terminal and crossing slots carry their exact normalization offset
at the common drawing period. -/
theorem values_forall₂_paddedCarrierNodeCandidateStream
    (field : Field) (period : Nat)
    (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors,
      descriptor.gridSize = period)
    (descriptorBounds : ∀ descriptor ∈ descriptors,
      descriptor.CoordinateBounds) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field period node)
      (paddedCarrierNodeCandidateStream descriptors)
      (values field descriptors) := by
  unfold paddedCarrierNodeCandidateStream values terminalValues
    crossingValues
  exact List.Forall₂.append
    (RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream_normalizationOffset_forall₂
      field period descriptors periodEq descriptorBounds)
    (RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream_normalizationOffset_forall₂
      field period descriptors periodEq)

end CarrierNormalizationOffsetCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing
