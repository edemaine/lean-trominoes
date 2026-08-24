/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeAlignmentSemantics

/-! # Guarded words of padded terminal carrier-key candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateWords
open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairFieldTags

/-- Batched terminal recipes emit exactly the guarded words of the existing
padded terminal candidate block. -/
theorem terminalCarrierKeyGuardedWords_descriptorPairTokens
    (pair : RouteDescriptor × RouteDescriptor) :
    terminalCarrierKeyGuardedWords (descriptorPairTokens pair) =
      (paddedTerminalCarrierKeyCandidates pair).map
        (guardedWord CarrierKeyWords.word) := by
  unfold terminalCarrierKeyGuardedWords
    paddedTerminalCarrierKeyCandidates
  exact words_eq_map_guardedWord_candidates
    (descriptorPairTokens pair)
    (terminalCarrierKeyActivations (descriptorPairTokens pair))
    terminalCarrierKeyRecipeBlocks
    (terminalCarrierKeyTemplateBlocks pair)
    (terminalCarrierKeyRecipeBlocks_match pair)

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
