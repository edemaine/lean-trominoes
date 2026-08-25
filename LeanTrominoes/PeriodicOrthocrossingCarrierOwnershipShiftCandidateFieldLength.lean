/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftCandidateAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierSourceKeyCandidateStreamData

/-! # Alignment length of ownership-shift candidate fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOwnershipShiftCandidateFieldStream

open CarrierOwnershipShiftField

theorem terminalValues_length
    (field : Field) (descriptors : List RouteDescriptor) :
    (terminalValues field descriptors).length =
      (RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
        descriptors).length := by
  unfold terminalValues
    RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
  induction (descriptors ×ˢ descriptors) with
  | nil => rfl
  | cons pair pairs induction =>
      simp only [List.flatMap_cons, List.length_append]
      rw [induction]
      exact congrArg
        (fun length => length +
          (pairs.flatMap
            RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidates).length)
        (RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidates_ownershipShift_forall₂
          field 0 pair).length_eq.symm

theorem crossingValues_length
    (field : Field) (descriptors : List RouteDescriptor) :
    (crossingValues field descriptors).length =
      (RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream
        descriptors).length := by
  unfold crossingValues
    RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream
  induction (RouteDescriptorOccurrenceSlotBinaryWords.taggedDescriptors
      descriptors ×ˢ
      RouteDescriptorOccurrenceSlotBinaryWords.taggedDescriptors
        descriptors) with
  | nil => rfl
  | cons pair pairs induction =>
      simp only [List.flatMap_cons, List.length_append]
      rw [induction]
      exact congrArg
        (fun length => length +
          (pairs.flatMap
            RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidates).length)
        (RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidates_ownershipShift_forall₂
          field pair).length_eq.symm

theorem valuesWithSentinel_length_sourceKeyCandidates
    (field : Field) (descriptors : List RouteDescriptor) :
    (valuesWithSentinel field descriptors).length =
      (paddedCarrierSourceKeyCandidateStream descriptors).length + 1 := by
  unfold valuesWithSentinel
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [show (values field descriptors).length =
      (paddedCarrierNodeCandidateStream descriptors).length by
    simp [values, paddedCarrierNodeCandidateStream,
      terminalValues_length, crossingValues_length]]
  simp [paddedCarrierSourceKeyCandidateStream]

end CarrierOwnershipShiftCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing
