/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateActiveMap
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCandidateWordData

/-! # Compact source-key candidates as active value maps -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNodeSourceKeyCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem sourceKeyCandidate_eq_mapActiveValue
    (candidate : Candidate CarrierNode) :
    sourceKeyCandidate candidate =
      candidate.mapActiveValue CarrierNodeSourceKeys.pair :=
  rfl

end CarrierNodeSourceKeyCandidateWords
end LeanTrominoes.PeriodicOrthocrossing
