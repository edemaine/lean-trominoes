/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyComponentStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftRecipeEmitterSemantics
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorNatStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorSignedWordCorrect
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyPairSelectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotBinaryWordPairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagSemantics

/-! # Semantics of shifted canonical crossing source-key component fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyComponentStream

open RouteDescriptorOccurrenceSlotBinaryWords

theorem fieldWordCorrect (field : CarrierKeyFieldProjector.Field) :
    CarrierKeyFieldProjector.WordCorrect field := by
  cases field <;>
    first
    | exact CarrierKeyFieldProjector.wordCorrect_route
    | exact CarrierKeyFieldProjector.wordCorrect_segment
    | exact CarrierKeyFieldProjector.wordCorrect_horizontalPositive
    | exact CarrierKeyFieldProjector.wordCorrect_horizontalNegative
    | exact CarrierKeyFieldProjector.wordCorrect_verticalPositive
    | exact CarrierKeyFieldProjector.wordCorrect_verticalNegative

/-- The unmerged mapper emits exactly two guarded component words per padded
shift candidate. -/
@[simp] theorem emittedStream_encodeDescriptorSlotPairs
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    emittedStream
        (RouteDescriptorOccurrenceSlotPairFieldTags.encodeDescriptorSlotPairs
          pairs) =
      DelimitedBinaryWords.encode
        (DelimitedBinaryWordGuardedPairMerge.componentWords
          (componentPairs pairs)) := by
  unfold emittedStream
  rw [RouteDescriptorOccurrenceSlotPairFieldTags.mappedOutput_encodeDescriptorSlotPairs]
  unfold componentPairs carrierNodeCandidates
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      rw [List.flatMap_cons,
        CanonicalCrossingShiftLeftSourceKeyRecipeEmitter.emittedTokens_descriptorSlotPairTokens,
        ← RouteDescriptorOccurrenceSlotCrossing.componentWords_canonicalCrossingShiftLeftCarrierNodeCandidates]
      simpa [DelimitedBinaryWords.encode,
        DelimitedBinaryWordGuardedPairMerge.componentWords,
        CarrierNodeSourceKeyCandidateWords.componentPairs,
        List.flatMap_assoc] using induction

@[simp] theorem emittedDescriptorStream_descriptorWords
    (descriptors : List RouteDescriptor) :
    emittedDescriptorStream (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        (DelimitedBinaryWordGuardedPairMerge.componentWords
          (componentPairs
            (taggedDescriptors descriptors ×ˢ
              taggedDescriptors descriptors))) := by
  unfold emittedDescriptorStream
  rw [expandedPairs_descriptorWords,
    RouteDescriptorOccurrenceSlotPairFieldTags.inputTokens_wordPairs,
    emittedStream_encodeDescriptorSlotPairs]

/-- Pair selection exposes one guarded optional carrier key for every padded
candidate. -/
@[simp] theorem selectedStream_descriptorWords
    (side : DelimitedBinaryWordPairSelector.Side)
    (descriptors : List RouteDescriptor) :
    selectedStream side (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨(selectedKeys side
          (taggedDescriptors descriptors ×ˢ
            taggedDescriptors descriptors)).map
              CarrierKeyFieldProjector.semanticWord⟩ := by
  unfold selectedStream selectedKeys
  rw [emittedDescriptorStream_descriptorWords,
    DelimitedBinaryWordPairSelector.tokens_encode_componentWords]
  have selected :=
    CarrierNodeSourceKeyCandidateWords.selectedWords_componentPairs
      side (carrierNodeCandidates
        (taggedDescriptors descriptors ×ˢ
          taggedDescriptors descriptors))
  have sourceKeyEq :
      sourceKey side = CarrierCrossingRecordSourceField.sourceKey side := by
    funext node
    cases side <;> rfl
  rw [sourceKeyEq]
  simpa [componentPairs, Function.comp_def] using
    congrArg DelimitedBinaryWords.encode selected

/-- Projecting a fixed component field yields the exact aligned candidate
column plus the rejection sentinel. -/
@[simp] theorem fieldStream_descriptorWords
    (side : DelimitedBinaryWordPairSelector.Side)
    (field : CarrierKeyFieldProjector.Field)
    (descriptors : List RouteDescriptor) :
    fieldStream side field (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        (fieldValuesWithSentinel side field
          (taggedDescriptors descriptors ×ˢ
            taggedDescriptors descriptors)) := by
  unfold fieldStream fieldValuesWithSentinel
  rw [selectedStream_descriptorWords]
  exact CarrierKeyFieldProjector.output_encode_semanticWords
    field (fieldWordCorrect field)
      (selectedKeys side
        (taggedDescriptors descriptors ×ˢ
          taggedDescriptors descriptors))

end CanonicalCrossingShiftLeftSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing
