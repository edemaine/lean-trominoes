/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisValueCandidateLength

/-! # Terminal carrier-key axis-stream length -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Pairwise terminal axis/candidate alignment extends to the complete
descriptor-square stream. -/
theorem terminalCarrierKeyAxisValueStream_length
    (descriptors : List RouteDescriptor) :
    ((descriptors ×ˢ descriptors).flatMap fun pair =>
        terminalCarrierKeyAxisValues
          (descriptorPairTokens pair)).length =
      (paddedTerminalCarrierKeyCandidateStream descriptors).length := by
  unfold paddedTerminalCarrierKeyCandidateStream
  generalize descriptors ×ˢ descriptors = pairs
  induction pairs with
  | nil => simp only [List.flatMap_nil, List.length_nil]
  | cons pair pairs induction =>
      simp only [List.flatMap_cons, List.length_append]
      rw [terminalCarrierKeyAxisValues_candidate_length, induction]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
