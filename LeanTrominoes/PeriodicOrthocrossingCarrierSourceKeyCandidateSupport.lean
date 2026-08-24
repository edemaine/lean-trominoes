/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierSourceKeyCandidateStreamData

/-! # Activity support of one compact source-key candidate -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem sourceKeyCandidate_supported_eq_isSome
    (candidate : Candidate CarrierNode) :
    (CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate candidate).supported =
      (CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate candidate).value.isSome := by
  rcases candidate with ⟨value, supported⟩
  cases value <;> rfl

end LeanTrominoes.PeriodicOrthocrossing
