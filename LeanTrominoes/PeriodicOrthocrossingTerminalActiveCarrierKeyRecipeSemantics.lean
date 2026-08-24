/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyRecipeData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyActiveRecipeWordSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeSlotData
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierNodeKeyTemplateBlockSemantics

/-! # Activity-supported terminal carrier-key word semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedCandidateWords
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairFieldTags

/-- Activity-supported recipes emit the physical key of every active padded
terminal carrier-node slot. -/
theorem terminalActiveCarrierKeyGuardedWords_descriptorPairTokens
    (pair : RouteDescriptor × RouteDescriptor) :
    terminalActiveCarrierKeyGuardedWords (descriptorPairTokens pair) =
      ((paddedTerminalCarrierNodeCandidates pair).map
        (Candidate.mapActiveValue CarrierNode.carrierKey)).map
          (guardedWord CarrierKeyWords.word) := by
  unfold terminalActiveCarrierKeyGuardedWords
    paddedTerminalCarrierNodeCandidates
  rw [words_forceSupportedBlocks_eq_map_guardedWord_candidates]
  rw [map_map_template_terminalCarrierKeyRecipeBlocks]
  rw [← map_carrierKey_terminalCarrierNodeTemplateBlocks]
  simp only [List.map_map, Function.comp_def]
  change
    (candidates
      (terminalCarrierKeyActivations (descriptorPairTokens pair))
      ((terminalCarrierNodeTemplateBlocks pair).map fun block =>
        block.map (Template.mapActiveValue CarrierNode.carrierKey))).map
        (guardedWord CarrierKeyWords.word) = _
  rw [← candidates_mapActiveValue]
  simp [List.map_map, Function.comp_def]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
