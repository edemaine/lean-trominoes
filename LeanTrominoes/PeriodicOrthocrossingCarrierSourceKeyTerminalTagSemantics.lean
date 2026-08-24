/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordPairCrossingSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagSemantics

/-! # Canonical terminal tags of the source-key component stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyComponentStream

@[simp] theorem terminalTags_descriptorWords
    (descriptors : List RouteDescriptor) :
    terminalTags (RouteDescriptorBinaryWords.words descriptors) =
      RouteDescriptorPairFieldTags.encodeDescriptorPairs
        (descriptors ×ˢ descriptors) := by
  unfold terminalTags
  rw [RouteDescriptorBinaryWordPairs.pairProduct_words_eq_descriptorWordPairs,
    RouteDescriptorPairFieldTags.inputTokens_descriptorWordPairs]

end CarrierSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing
