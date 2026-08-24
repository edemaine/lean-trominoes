/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisTerminalTagCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordPairCrossingSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagSemantics

/-! # Canonical terminal-pair tag semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisTerminalTags

@[simp] theorem tags_descriptorWords
    (descriptors : List RouteDescriptor) :
    tags (RouteDescriptorBinaryWords.words descriptors) =
      RouteDescriptorPairFieldTags.encodeDescriptorPairs
        (descriptors ×ˢ descriptors) := by
  unfold tags
  rw [RouteDescriptorBinaryWordPairs.pairProduct_words_eq_descriptorWordPairs,
    RouteDescriptorPairFieldTags.inputTokens_descriptorWordPairs]

end CarrierKeyAxisTerminalTags
end LeanTrominoes.PeriodicOrthocrossing
