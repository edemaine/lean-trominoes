/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierIdentityCandidateStreamData

/-! # Exact active values of padded carrier identities -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

theorem filterMap_value_map_identityCandidate
    (candidates : List (Candidate CarrierNodeRankDatum)) :
    (candidates.map CarrierNodeRankDatum.identityCandidate).filterMap
        Candidate.value =
      (candidates.filterMap Candidate.value).map
        CarrierNodeRankDatum.identity := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      rcases candidate with ⟨value, supported⟩
      cases value <;>
        simp [CarrierNodeRankDatum.identityCandidate, induction]

/-- Compacting the padded identity stream commutes exactly with identity
projection from the compacted rank-data stream. -/
theorem paddedCarrierIdentityCandidateStream_filterMap
    (period : Nat) (descriptors : List RouteDescriptor) :
    (paddedCarrierIdentityCandidateStreamAtPeriod
        period descriptors).filterMap Candidate.value =
      ((paddedCarrierRankDatumCandidateStreamAtPeriod
        period descriptors).filterMap Candidate.value).map
          CarrierNodeRankDatum.identity := by
  unfold paddedCarrierIdentityCandidateStreamAtPeriod
  exact filterMap_value_map_identityCandidate _

end LeanTrominoes.PeriodicOrthocrossing
