/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisStreamLength

/-! # Sentinel-completed carrier-key axis-stream length -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisStream

/-- Appending the zero sentinel aligns the axis values with the extra
rejection-guard column of every representative row. -/
theorem valuesWithSentinel_length (descriptors : List RouteDescriptor) :
    (valuesWithSentinel descriptors).length =
      (paddedCarrierKeyCandidateStream descriptors).length + 1 := by
  simp [valuesWithSentinel, values_length]

end CarrierKeyAxisStream
end LeanTrominoes.PeriodicOrthocrossing
