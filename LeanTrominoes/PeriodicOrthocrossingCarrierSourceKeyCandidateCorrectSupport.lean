/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateSelfSupport
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyCandidateStreamSupport

/-! # Correct support of the compact source-key candidate stream -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

theorem paddedCarrierSourceKeyCandidateStream_correctSupport
    (descriptors : List RouteDescriptor) :
    CorrectSupport
      ((paddedCarrierSourceKeyCandidateStream descriptors).filterMap
        Candidate.value)
      (paddedCarrierSourceKeyCandidateStream descriptors) :=
  correctSupport_filterMap_of_supported_eq_isSome _
    (paddedCarrierSourceKeyCandidateStream_supported_eq_isSome descriptors)

end LeanTrominoes.PeriodicOrthocrossing
