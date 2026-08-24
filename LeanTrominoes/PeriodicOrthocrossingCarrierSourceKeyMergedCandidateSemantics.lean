/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeEncodingSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCandidateListSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentCandidateTokenSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyMergedStreamData

/-! # Exact padded-candidate semantics of the merged source-key stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyMergedStream

/-- On canonical descriptor words, the physical pair merger emits exactly
one guarded compact source-key word per padded carrier-node candidate. -/
@[simp] theorem tokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    tokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        (CarrierNodeSourceKeyCandidateWords.mergedWords
          (paddedCarrierNodeCandidateStream descriptors)) := by
  unfold tokens
  rw [CarrierSourceKeyComponentStream.tokens_descriptorWords_eq_componentWords,
    DelimitedBinaryWordGuardedPairMerge.tokens_encode_componentWords,
    CarrierNodeSourceKeyCandidateWords.guardedPairMergedWords_componentPairs]

end CarrierSourceKeyMergedStream
end LeanTrominoes.PeriodicOrthocrossing
