/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointTerminalValueSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData

/-! # Complete crossing-point candidate fields aligned with semantic nodes -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingPointCandidateFieldStream

open CarrierCrossingPointField
open PaddedSupportedLastRepresentativeEqualityRows

private theorem candidates_forall₂_optionalNodeValues
    (field : Field) (candidates : List (Candidate CarrierNode)) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = nodeValue field node)
      candidates
      ((PaddedSupportedLastRepresentativeEqualityRows.values
        candidates).map (optionalNodeValue field)) := by
  unfold PaddedSupportedLastRepresentativeEqualityRows.values
  induction candidates with
  | nil => exact List.Forall₂.nil
  | cons candidate candidates induction =>
      simp only [List.map_cons]
      exact List.Forall₂.cons
        (by
          intro node valueEq
          rw [valueEq]
          rfl)
        induction

theorem terminalValues_forall₂
    (field : Field) (descriptors : List RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = nodeValue field node)
      (RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
        descriptors)
      (terminalValues descriptors) := by
  rw [terminalValues_eq_optionalNodeValues field descriptors]
  exact candidates_forall₂_optionalNodeValues field _

/-- Terminal and crossing-point fields agree with every active semantic node;
inactive padding may carry arbitrary affine values. -/
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
    (RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream_point_forall₂
      field descriptors)

end CarrierCrossingPointCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end
