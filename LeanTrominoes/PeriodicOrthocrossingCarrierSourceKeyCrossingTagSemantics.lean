/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotBinaryWordPairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagSemantics

/-! # Canonical crossing tags of the source-key component stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyComponentStream

open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem crossingTags_descriptorWords
    (descriptors : List RouteDescriptor) :
    crossingTags (RouteDescriptorBinaryWords.words descriptors) =
      RouteDescriptorOccurrenceSlotPairFieldTags.encodeDescriptorSlotPairs
        (taggedDescriptors descriptors ×ˢ
          taggedDescriptors descriptors) := by
  unfold crossingTags
  rw [expandedPairs_descriptorWords,
    RouteDescriptorOccurrenceSlotPairFieldTags.inputTokens_wordPairs]

end CarrierSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing
