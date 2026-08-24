/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierIdentityActiveCandidateSemantics

/-! # Carrier identity candidate streams as active node-code maps -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

theorem paddedCarrierIdentityCandidateStreamAtPeriod_eq_mapActiveValue
    (period : Nat) (descriptors : List RouteDescriptor) :
    paddedCarrierIdentityCandidateStreamAtPeriod period descriptors =
      (paddedCarrierNodeCandidateStream descriptors).map
        (Candidate.mapActiveValue CarrierNode.code) := by
  unfold paddedCarrierIdentityCandidateStreamAtPeriod
    paddedCarrierRankDatumCandidateStreamAtPeriod
  rw [List.map_map]
  apply List.map_congr_left
  intro candidate _candidateMember
  exact CarrierNodeRankDatum.identityCandidate_mapValue_rankDatum
    period candidate

end LeanTrominoes.PeriodicOrthocrossing
