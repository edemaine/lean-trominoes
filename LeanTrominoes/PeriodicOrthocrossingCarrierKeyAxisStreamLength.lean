/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisStreamData
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisValueStreamLength
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisValueStreamLength

/-! # Complete carrier-key axis/candidate stream length -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisStream

/-- The complete terminal-prefix/crossing-suffix axis stream has exactly one
value for every padded carrier-key candidate. -/
theorem values_length (descriptors : List RouteDescriptor) :
    (values descriptors).length =
      (paddedCarrierKeyCandidateStream descriptors).length := by
  unfold values terminalValues crossingValues
    paddedCarrierKeyCandidateStream
  rw [List.length_append, List.length_append,
    RouteDescriptorPairAffine.terminalCarrierKeyAxisValueStream_length,
    RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyAxisValueStream_length]

end CarrierKeyAxisStream
end LeanTrominoes.PeriodicOrthocrossing
