/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computation.Encoding.Fixed.FixedAxisUnaryFieldsLength
import LeanTrominoes.Common.List.ListForallTwoFlattenLength
import LeanTrominoes.Computation.Encoding.Padded.PaddedSupportedCandidateBlockLength
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeAlignmentSemantics
import LeanTrominoes.Graphs.Drawings.Orthogonal.Terminal.PeriodicOrthocrossingTerminalCarrierKeyAxisValueLength

/-! # Terminal carrier-key axis/candidate length alignment -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- There is one terminal axis value for every padded terminal carrier-key
candidate of a descriptor pair. -/
theorem terminalCarrierKeyAxisValues_candidate_length
    (pair : RouteDescriptor × RouteDescriptor) :
    (terminalCarrierKeyAxisValues (descriptorPairTokens pair)).length =
      (paddedTerminalCarrierKeyCandidates pair).length := by
  unfold terminalCarrierKeyAxisValues
  rw [FixedAxisUnaryFields.values_length_of_length_eq _ _
    (terminalCarrierKeyExpandedActives_axis_length
      (descriptorPairTokens pair))]
  rw [terminalCarrierKeyRecipeAxes_length]
  unfold paddedTerminalCarrierKeyCandidates
  rw [PaddedSupportedCandidateBlocks.candidates_length_of_length_eq]
  · exact List.Forall₂.flatten_length_eq
      (terminalCarrierKeyRecipeBlocks_match pair)
  · rw [terminalCarrierKeyActivations_length]
    exact (terminalCarrierKeyRecipeBlocks_match pair).length_eq

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
