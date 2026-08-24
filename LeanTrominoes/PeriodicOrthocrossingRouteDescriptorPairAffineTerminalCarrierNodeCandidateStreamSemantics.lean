/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockActivity
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeStreamData

/-! # Activity semantics of terminal carrier-node candidate streams -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairFieldTags

/-- Filtering inactive slots from the padded descriptor-square stream gives
its exact compact terminal-node active-value stream. -/
theorem filterMap_paddedTerminalCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    (paddedTerminalCarrierNodeCandidateStream descriptors).filterMap
        Candidate.value =
      (descriptors ×ˢ descriptors).flatMap fun pair =>
        activeValues
          (terminalCarrierKeyActivations (descriptorPairTokens pair))
          (terminalCarrierNodeTemplateBlocks pair) := by
  unfold paddedTerminalCarrierNodeCandidateStream
    paddedTerminalCarrierNodeCandidates
  exact filterMap_value_flatMap_candidates
    (descriptors ×ˢ descriptors)
    (fun pair =>
      terminalCarrierKeyActivations (descriptorPairTokens pair))
    terminalCarrierNodeTemplateBlocks

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
