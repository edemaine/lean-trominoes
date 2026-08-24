/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisCrossingTagCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotBinaryWordPairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagSemantics

/-! # Canonical crossing-slot-pair tag semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisCrossingTags

open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem tags_descriptorWords
    (descriptors : List RouteDescriptor) :
    tags (RouteDescriptorBinaryWords.words descriptors) =
      RouteDescriptorOccurrenceSlotPairFieldTags.encodeDescriptorSlotPairs
        (taggedDescriptors descriptors ×ˢ
          taggedDescriptors descriptors) := by
  unfold tags
  rw [expandedPairs_descriptorWords,
    RouteDescriptorOccurrenceSlotPairFieldTags.inputTokens_wordPairs]

end CarrierKeyAxisCrossingTags
end LeanTrominoes.PeriodicOrthocrossing
