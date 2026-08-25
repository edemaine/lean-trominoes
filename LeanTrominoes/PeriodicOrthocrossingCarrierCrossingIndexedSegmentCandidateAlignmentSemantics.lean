/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentCandidateFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalZeroFieldAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData

/-! # Complete indexed crossing-segment fields aligned with carrier nodes -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingIndexedSegmentCandidateFieldStream

open CarrierCrossingIndexedSegmentField
open PaddedSupportedLastRepresentativeEqualityRows

theorem terminalValues_forall₂
    (field : Field) (descriptors : List RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = nodeValue field node)
      (RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
        descriptors)
      (terminalValues descriptors) := by
  unfold terminalValues
  exact RouteDescriptorPairAffine.terminalZeroFields_forall₂
    (nodeValue field) (fun _ => rfl) descriptors

/-- Active terminal and crossing slots carry their exact indexed-segment
field. Inactive crossing slots may contain arbitrary affine values. -/
theorem values_forall₂_paddedCarrierNodeCandidateStream
    (field : Field) (descriptors : List RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = nodeValue field node)
      (paddedCarrierNodeCandidateStream descriptors)
      (values field descriptors) := by
  unfold paddedCarrierNodeCandidateStream values crossingValues
  exact List.Forall₂.append
    (terminalValues_forall₂ field descriptors)
    (RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream_indexedSegment_forall₂
      field descriptors)

end CarrierCrossingIndexedSegmentCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end
