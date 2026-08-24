/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyActiveCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierSourceKeyCandidateStreamData

/-! # Compact source-key candidate streams as active value maps -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

theorem paddedCarrierSourceKeyCandidateStream_eq_mapActiveValue
    (descriptors : List RouteDescriptor) :
    paddedCarrierSourceKeyCandidateStream descriptors =
      (paddedCarrierNodeCandidateStream descriptors).map
        (Candidate.mapActiveValue CarrierNodeSourceKeys.pair) := by
  unfold paddedCarrierSourceKeyCandidateStream
  apply List.map_congr_left
  intro candidate _candidateMember
  exact
    CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate_eq_mapActiveValue
      candidate

end LeanTrominoes.PeriodicOrthocrossing
