/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateActiveMap
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierIdentityCandidateStreamData

/-! # Carrier identity candidates as active node-code maps -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem CarrierNodeRankDatum.identityCandidate_mapValue_rankDatum
    (period : Nat) (candidate : Candidate CarrierNode) :
    CarrierNodeRankDatum.identityCandidate
        (candidate.mapValue (carrierNodeRankDatumAtPeriod period)) =
      candidate.mapActiveValue CarrierNode.code := by
  rcases candidate with ⟨value, supported⟩
  cases value <;> rfl

end LeanTrominoes.PeriodicOrthocrossing
