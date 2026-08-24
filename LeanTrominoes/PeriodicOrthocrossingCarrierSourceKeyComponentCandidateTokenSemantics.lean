/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentStreamSemantics

/-! # Physical source-key components as padded node candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyComponentStream

@[simp] theorem tokens_descriptorWords_eq_componentWords
    (descriptors : List RouteDescriptor) :
    tokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        (DelimitedBinaryWordGuardedPairMerge.componentWords
          (CarrierNodeSourceKeyCandidateWords.componentPairs
            (paddedCarrierNodeCandidateStream descriptors))) := by
  rw [tokens_descriptorWords,
    componentWords_paddedCarrierNodeCandidateStream]

end CarrierSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing
