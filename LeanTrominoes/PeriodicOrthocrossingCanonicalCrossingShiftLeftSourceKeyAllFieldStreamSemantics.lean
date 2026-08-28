/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyAllFieldStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyComponentStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorStreamSemantics

/-! # Semantics of all shifted canonical crossing source-key pair fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyAllFieldStream

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords

private theorem componentWords_eq_semanticWords
    (candidates : List (Candidate CarrierNode)) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        (CarrierNodeSourceKeyCandidateWords.componentPairs candidates) =
      ⟨(values candidates).flatMap fun node =>
        [CarrierKeyFieldProjector.semanticWord
            (node.map
              (CanonicalCrossingShiftLeftSourceKeyComponentStream.sourceKey
                .first)),
          CarrierKeyFieldProjector.semanticWord
            (node.map
              (CanonicalCrossingShiftLeftSourceKeyComponentStream.sourceKey
                .second))]⟩ := by
  apply congrArg DelimitedBinaryWords.Input.mk
  unfold CarrierNodeSourceKeyCandidateWords.componentPairs
    PaddedSupportedLastRepresentativeEqualityRows.values
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      rcases candidate with ⟨value, supported⟩
      cases value <;>
        simp [CarrierNodeSourceKeyCandidateWords.componentPair,
          PaddedSupportedCandidateWords.sentinelWord,
          CanonicalCrossingShiftLeftSourceKeyComponentStream.sourceKey,
          CarrierKeyFieldProjector.semanticWord, induction]

theorem emittedComponentStream_descriptorWords
    (descriptors : List RouteDescriptor) :
    CanonicalCrossingShiftLeftSourceKeyComponentStream.emittedDescriptorStream
        (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨(componentKeys
          (taggedDescriptors descriptors ×ˢ
            taggedDescriptors descriptors)).map
              CarrierKeyFieldProjector.semanticWord⟩ := by
  rw [CanonicalCrossingShiftLeftSourceKeyComponentStream.emittedDescriptorStream_descriptorWords]
  unfold componentKeys
    CanonicalCrossingShiftLeftSourceKeyComponentStream.componentPairs
  rw [componentWords_eq_semanticWords]
  rw [List.map_flatMap]
  rfl

/-- The physical stream is exactly the candidate-major twelve-field source
pair table followed by its twelve-zero rejection sentinel. -/
@[simp] theorem emittedFields_descriptorWords
    (descriptors : List RouteDescriptor) :
    emittedFields (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        (fieldValuesWithSentinel
          (taggedDescriptors descriptors ×ˢ
            taggedDescriptors descriptors)) := by
  unfold emittedFields fieldValuesWithSentinel
  rw [emittedComponentStream_descriptorWords,
    CarrierKeyAllFieldProjector.output_encode_semanticWords]

end CanonicalCrossingShiftLeftSourceKeyAllFieldStream
end LeanTrominoes.PeriodicOrthocrossing
