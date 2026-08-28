/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyAllFieldStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentCandidateTokenSemantics

/-! # Semantics of all padded carrier-node source-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyAllFieldStream

open PaddedSupportedLastRepresentativeEqualityRows

private theorem componentWords_eq_semanticWords
    (candidates : List (Candidate CarrierNode)) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        (CarrierNodeSourceKeyCandidateWords.componentPairs candidates) =
      ⟨((values candidates).flatMap fun node =>
        [node.map fun value => (CarrierNodeSourceKeys.pair value).1,
          node.map fun value => (CarrierNodeSourceKeys.pair value).2]).map
            CarrierKeyFieldProjector.semanticWord⟩ := by
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
          CarrierKeyFieldProjector.semanticWord, induction]

/-- The physical projection is exactly the candidate-major twelve-field
source-key table followed by its twelve-zero sentinel. -/
@[simp] theorem emittedFields_eq
    (descriptors : List RouteDescriptor) :
    emittedFields descriptors =
      UnaryFieldEncoderMachine.unaryFields
        (fieldValuesWithSentinel descriptors) := by
  unfold emittedFields fieldValuesWithSentinel componentKeys
  rw [CarrierSourceKeyComponentStream.tokens_descriptorWords_eq_componentWords,
    componentWords_eq_semanticWords,
    CarrierKeyAllFieldProjector.output_encode_semanticWords]

end CarrierSourceKeyAllFieldStream
end LeanTrominoes.PeriodicOrthocrossing
