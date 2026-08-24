/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierRankDatumCandidateStreamData

/-! # Active carrier identities aligned with padded rank data -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- Project one padded rank-datum slot to its reversible identity and replace
the unrelated retained-key support tag by exact slot activity. -/
def CarrierNodeRankDatum.identityCandidate
    (candidate : Candidate CarrierNodeRankDatum) :
    Candidate CarrierNodeCode where
  value := candidate.value.map CarrierNodeRankDatum.identity
  supported := candidate.value.isSome

/-- Carrier identities in exact alignment with the padded rank-data stream. -/
def paddedCarrierIdentityCandidateStreamAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    List (Candidate CarrierNodeCode) :=
  (paddedCarrierRankDatumCandidateStreamAtPeriod period descriptors).map
    CarrierNodeRankDatum.identityCandidate

end LeanTrominoes.PeriodicOrthocrossing

end
