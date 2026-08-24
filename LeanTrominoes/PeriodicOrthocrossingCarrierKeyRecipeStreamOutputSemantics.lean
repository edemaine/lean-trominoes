/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamOutput
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamSemantics

/-! # Canonical semantics of the total recipe-stream output -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeStream

@[simp] theorem output_descriptorWords
    (descriptors : List RouteDescriptor) :
    output (RouteDescriptorBinaryWords.words descriptors) =
      ⟨guardedWords descriptors⟩ := by
  have encodedEq :
      DelimitedBinaryWords.encode
          (output (RouteDescriptorBinaryWords.words descriptors)) =
        DelimitedBinaryWords.encode ⟨guardedWords descriptors⟩ := by
    rw [← emittedTokens_eq_encode_output,
      emittedTokens_descriptorWords]
  have decodedEq := congrArg DelimitedBinaryWords.decode encodedEq
  simpa using decodedEq

@[simp] theorem output_descriptorWords_eq_paddedCandidates
    (descriptors : List RouteDescriptor) :
    output (RouteDescriptorBinaryWords.words descriptors) =
      ⟨(paddedCarrierKeyCandidateStream descriptors).map
        (PaddedSupportedCandidateWords.guardedWord CarrierKeyWords.word)⟩ := by
  rw [output_descriptorWords, guardedWords_eq_paddedCandidateStream]

end CarrierKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing
