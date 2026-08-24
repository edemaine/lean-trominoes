/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotPairProductCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotBinaryWordData

/-! # Exact ordered word pairs for fixed descriptor occurrence slots -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotBinaryWords

open DelimitedBinaryWordOccurrenceSlotTags

/-- Canonical word-pair input indexed by the row-major square of tagged
route descriptors. -/
def wordPairs (descriptors : List RouteDescriptor) :
    DelimitedBinaryWordPairs.Input :=
  ⟨(taggedDescriptors descriptors ×ˢ
      taggedDescriptors descriptors).map fun pair =>
    (descriptorSlotWord pair.1, descriptorSlotWord pair.2)⟩

/-- Expanding canonical descriptor words into slots and applying the generic
word-product compiler gives exactly the canonical tagged-descriptor square. -/
@[simp] theorem expandedPairs_descriptorWords
    (descriptors : List RouteDescriptor) :
    expandedPairs (RouteDescriptorBinaryWords.words descriptors) =
      wordPairs descriptors := by
  unfold expandedPairs
  rw [expandInput_descriptorWords]
  apply congrArg DelimitedBinaryWordPairs.Input.mk
  exact pairProduct_pairs descriptors

end RouteDescriptorOccurrenceSlotBinaryWords
end LeanTrominoes.PeriodicOrthocrossing
