/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeSlotData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairMatchStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipePairAlignmentSemantics

/-! # Terminal source-key recipe pairs as padded node candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs
open RouteDescriptorPairFieldTags

theorem terminalSourceKeyRecipePairWords_eq_candidates
    (pair : RouteDescriptor × RouteDescriptor) :
    RouteDescriptorPairSourceKeyRecipePairs.words
        (descriptorPairTokens pair)
        (terminalCarrierKeyActivations (descriptorPairTokens pair))
        terminalSourceKeyRecipePairBlocks =
      (paddedTerminalCarrierNodeCandidates pair).map
        CarrierNodeSourceKeyCandidateWords.componentPair := by
  unfold paddedTerminalCarrierNodeCandidates
  exact words_eq_map_componentPair_candidates
    (descriptorPairTokens pair)
    (terminalCarrierKeyActivations (descriptorPairTokens pair))
    terminalSourceKeyRecipePairBlocks
    (terminalCarrierNodeTemplateBlocks pair)
    (terminalSourceKeyRecipePairBlocks_matchNode pair)

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
