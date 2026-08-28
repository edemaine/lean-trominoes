/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyAllFieldStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyComponentCandidateSemantics

/-! # Semantics of normalized padded carrier source-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyAllFieldStream

open PaddedSupportedLastRepresentativeEqualityRows

private theorem componentWords_eq_semanticWords
    (period : Nat) (candidates : List (Candidate CarrierNode)) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        (candidates.map fun candidate =>
          CarrierNodeSourceKeyCandidateWords.componentPair
            (CarrierNormalizedSourceKeyRecipePairs.normalizeCandidateAtPeriod
              period candidate)) =
      ⟨(componentKeysOfCandidatesAtPeriod period candidates).map
        CarrierKeyFieldProjector.semanticWord⟩ := by
  apply congrArg DelimitedBinaryWords.Input.mk
  unfold componentKeysOfCandidatesAtPeriod
    PaddedSupportedLastRepresentativeEqualityRows.values
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      rcases candidate with ⟨value, supported⟩
      simp only [List.map_cons, List.flatMap_cons]
      rw [induction]
      cases value <;>
        simp [CarrierNormalizedSourceKeyRecipePairs.normalizeCandidateAtPeriod,
          Candidate.mapValue,
          CarrierNodeSourceKeyCandidateWords.componentPair,
          PaddedSupportedCandidateWords.sentinelWord,
          CarrierKeyFieldProjector.semanticWord,
          CarrierNodeNormalizedSourceKeys.pairAtPeriod]

@[simp] theorem emittedFields_eq
    (period : Nat) (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors,
      descriptor.gridSize = period) :
    emittedFields descriptors =
      UnaryFieldEncoderMachine.unaryFields
        (fieldValuesWithSentinelAtPeriod period descriptors) := by
  unfold emittedFields fieldValuesWithSentinelAtPeriod
    componentKeysAtPeriod
  rw [CarrierNormalizedSourceKeyComponentStream.tokens_descriptorWords_eq_normalizedCandidateComponentWords
      period descriptors periodEq]
  change CarrierKeyAllFieldProjector.output
      (DelimitedBinaryWords.encode
        (DelimitedBinaryWordGuardedPairMerge.componentWords
          ((paddedCarrierNodeCandidateStream descriptors).map fun candidate =>
            CarrierNodeSourceKeyCandidateWords.componentPair
              (CarrierNormalizedSourceKeyRecipePairs.normalizeCandidateAtPeriod
                period candidate)))) = _
  rw [componentWords_eq_semanticWords,
    CarrierKeyAllFieldProjector.output_encode_semanticWords]

end CarrierNormalizedSourceKeyAllFieldStream
end LeanTrominoes.PeriodicOrthocrossing
