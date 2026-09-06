/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamOutputSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamSentinelCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRepresentativeRowData

/-! # Canonical semantics of sentinel-completed carrier-key words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeStream

@[simp] theorem outputWithSentinel_descriptorWords
    (descriptors : List RouteDescriptor) :
    outputWithSentinel (RouteDescriptorBinaryWords.words descriptors) =
      PaddedSupportedCandidateWords.wordsWithSentinel CarrierKeyWords.word
        (paddedCarrierKeyCandidateStream descriptors) := by
  unfold outputWithSentinel
    PaddedSupportedCandidateWords.wordsWithSentinel rejectionSentinel
  rw [output_descriptorWords, guardedWords_eq_paddedCandidateStream]
  rfl

end CarrierKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing
