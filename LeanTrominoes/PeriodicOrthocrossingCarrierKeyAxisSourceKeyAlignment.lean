/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisStreamSentinelLength
import LeanTrominoes.PeriodicOrthocrossingCarrierCandidateStreamProjectionLength

/-! # Alignment of carrier-key axis values with source-key candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisStream

/-- The key-axis field has one value for every compact source-key candidate,
plus the rejection sentinel used by representative lookup. -/
theorem valuesWithSentinel_length_sourceKeyCandidates
    (descriptors : List RouteDescriptor) :
    (valuesWithSentinel descriptors).length =
      (paddedCarrierSourceKeyCandidateStream descriptors).length + 1 := by
  rw [valuesWithSentinel_length]
  rw [paddedCarrierKeyCandidateStream_length_eq_sourceKeyCandidates]

end CarrierKeyAxisStream
end LeanTrominoes.PeriodicOrthocrossing

end
