/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateSelfSupport
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierIdentityCandidateStreamData

/-! # Exact activity support of padded carrier identities -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem CarrierNodeRankDatum.identityCandidate_supported_eq_isSome
    (candidate : Candidate CarrierNodeRankDatum) :
    (CarrierNodeRankDatum.identityCandidate candidate).supported =
      (CarrierNodeRankDatum.identityCandidate candidate).value.isSome := by
  cases candidate with
  | mk value supported => cases value <;> rfl

theorem paddedCarrierIdentityCandidateStream_supported_eq_isSome
    (period : Nat) (descriptors : List RouteDescriptor) :
    ∀ candidate ∈
        paddedCarrierIdentityCandidateStreamAtPeriod period descriptors,
      candidate.supported = candidate.value.isSome := by
  intro candidate member
  rcases List.mem_map.mp member with ⟨datum, _datumMember, rfl⟩
  exact CarrierNodeRankDatum.identityCandidate_supported_eq_isSome datum

/-- The aligned identity stream is supported by exactly its own active
identities, so its representative rows deduplicate every active node. -/
theorem paddedCarrierIdentityCandidateStream_correctSupport
    (period : Nat) (descriptors : List RouteDescriptor) :
    CorrectSupport
      ((paddedCarrierIdentityCandidateStreamAtPeriod period descriptors).filterMap
        Candidate.value)
      (paddedCarrierIdentityCandidateStreamAtPeriod period descriptors) :=
  correctSupport_filterMap_of_supported_eq_isSome _
    (paddedCarrierIdentityCandidateStream_supported_eq_isSome
      period descriptors)

end LeanTrominoes.PeriodicOrthocrossing
