/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyGuardedWordData
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipePairCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipePairComponentSemantics

/-! # Paired semantics of terminal source-key guarded words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs
open RouteDescriptorPairFieldTags

theorem componentWords_terminalCandidates
    (pair : RouteDescriptor × RouteDescriptor) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        (CarrierNodeSourceKeyCandidateWords.componentPairs
          (paddedTerminalCarrierNodeCandidates pair)) =
      ⟨terminalSourceKeyGuardedWords (descriptorPairTokens pair)⟩ := by
  unfold CarrierNodeSourceKeyCandidateWords.componentPairs
  rw [← terminalSourceKeyRecipePairWords_eq_candidates,
    componentWords_words,
    componentRecipeBlocks_terminalSourceKeyRecipePairBlocks]
  rfl

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
