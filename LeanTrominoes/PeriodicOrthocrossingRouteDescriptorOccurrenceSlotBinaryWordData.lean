/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotTags
import LeanTrominoes.DelimitedBinaryWordPairProductMachine
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordData

/-! # Binary words indexed by fixed route-descriptor occurrence slots -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotBinaryWords

open DelimitedBinaryWordOccurrenceSlotTags

/-- A descriptor paired with one of its eighty-one fixed occurrence slots. -/
abbrev TaggedDescriptor :=
  RouteDescriptor × DelimitedBinaryWordOccurrenceSlotTags.Slot

/-- Descriptor-major enumeration with increasing slot index inside every
descriptor block. -/
def taggedDescriptors (descriptors : List RouteDescriptor) :
    List TaggedDescriptor :=
  descriptors.flatMap fun descriptor =>
    (List.finRange 81).map fun slot => (descriptor, slot)

/-- Canonical descriptor word with its twelfth unary slot field. -/
def descriptorSlotWord (tagged : TaggedDescriptor) : List Bool :=
  slotWord tagged.2
    (RouteDescriptorBinaryWords.descriptorWord tagged.1)

/-- Canonical binary-word input for all fixed descriptor occurrence slots. -/
def words (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  ⟨(taggedDescriptors descriptors).map descriptorSlotWord⟩

/-- The generic eighty-one-copy expansion of canonical descriptor words is
exactly the descriptor-major tagged-slot word list. -/
@[simp] theorem expandInput_descriptorWords
    (descriptors : List RouteDescriptor) :
    expandInput (RouteDescriptorBinaryWords.words descriptors) =
      words descriptors := by
  apply congrArg DelimitedBinaryWords.Input.mk
  simp [RouteDescriptorBinaryWords.words, taggedDescriptors,
    descriptorSlotWord, List.flatMap_map,
    List.map_flatMap, List.map_map, Function.comp_def]

theorem product_map_map
    (firsts : List α) (seconds : List β)
    (firstMap : α → γ) (secondMap : β → δ) :
    (firsts.map firstMap ×ˢ seconds.map secondMap) =
      (firsts ×ˢ seconds).map fun pair =>
        (firstMap pair.1, secondMap pair.2) := by
  induction firsts with
  | nil => rfl
  | cons first firsts induction =>
      simp only [List.map_cons, List.product_cons, List.map_append,
        List.map_map, Function.comp_def, induction]

/-- The row-major word product carries the exact row-major square of tagged
descriptors, hence has order `descriptor₁, slot₁, descriptor₂, slot₂`. -/
theorem pairProduct_pairs (descriptors : List RouteDescriptor) :
    (DelimitedBinaryWordPairProductMachine.pairs
        (words descriptors)).pairs =
      (taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors).map fun pair =>
          (descriptorSlotWord pair.1, descriptorSlotWord pair.2) := by
  unfold DelimitedBinaryWordPairProductMachine.pairs words
  exact product_map_map
    (taggedDescriptors descriptors) (taggedDescriptors descriptors)
    descriptorSlotWord descriptorSlotWord

end RouteDescriptorOccurrenceSlotBinaryWords
end LeanTrominoes.PeriodicOrthocrossing
