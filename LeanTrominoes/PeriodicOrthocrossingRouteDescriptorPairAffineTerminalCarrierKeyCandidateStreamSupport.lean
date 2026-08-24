/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockSelfSupport
import LeanTrominoes.PaddedSupportedCandidateSelfSupport
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotSupport

/-! # Support of padded terminal carrier-key candidate streams -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

/-- Every padded terminal candidate is supported exactly when it is active. -/
theorem paddedTerminalCarrierKeyCandidateStream_supported_eq_isSome
    (descriptors : List RouteDescriptor) :
    ∀ candidate ∈ paddedTerminalCarrierKeyCandidateStream descriptors,
      candidate.supported = candidate.value.isSome := by
  unfold paddedTerminalCarrierKeyCandidateStream
  apply flatMap_candidates_supported_eq_isSome
  intro pair _pairMember
  unfold paddedTerminalCarrierKeyCandidates
  apply candidates_supported_eq_isSome
  exact terminalCarrierKeyTemplateBlocks_supported_true pair

/-- Hence the padded terminal stream is correctly supported by its own
ordered active-value projection. -/
theorem paddedTerminalCarrierKeyCandidateStream_correctSupport
    (descriptors : List RouteDescriptor) :
    CorrectSupport
      ((paddedTerminalCarrierKeyCandidateStream descriptors).filterMap
        Candidate.value)
      (paddedTerminalCarrierKeyCandidateStream descriptors) := by
  exact correctSupport_filterMap_of_supported_eq_isSome _
    (paddedTerminalCarrierKeyCandidateStream_supported_eq_isSome
      descriptors)

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
