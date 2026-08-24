/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeKeyCandidateStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierSourceKeyCandidateStreamData

/-! # Length preservation under carrier candidate projections -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Carrier keys and compact source keys both project the same padded
carrier-node stream, so their candidate counts agree. -/
theorem paddedCarrierKeyCandidateStream_length_eq_sourceKeyCandidates
    (descriptors : List RouteDescriptor) :
    (paddedCarrierKeyCandidateStream descriptors).length =
      (paddedCarrierSourceKeyCandidateStream descriptors).length := by
  unfold paddedCarrierSourceKeyCandidateStream
  rw [List.length_map]
  rw [← map_carrierKey_paddedCarrierNodeCandidateStream]
  rw [List.length_map]

end LeanTrominoes.PeriodicOrthocrossing

end
