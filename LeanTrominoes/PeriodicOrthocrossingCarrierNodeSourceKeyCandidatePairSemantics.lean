/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCandidateWordData

/-! # Semantics of one padded carrier-node source-key pair -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNodeSourceKeyCandidateWords

open PaddedSupportedCandidateWords
open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem mergePair_componentPair
    (candidate : Candidate CarrierNode) :
    DelimitedBinaryWordGuardedPairMerge.mergePair
        (componentPair candidate).1 (componentPair candidate).2 =
      guardedWord CarrierNodeSourceKeys.word
        (sourceKeyCandidate candidate) := by
  rcases candidate with ⟨value, supported⟩
  cases value <;>
    simp [componentPair, sourceKeyCandidate, guardedWord, sentinelWord,
      DelimitedBinaryWordGuardedPairMerge.mergePair,
      CarrierNodeSourceKeys.word]

end CarrierNodeSourceKeyCandidateWords
end LeanTrominoes.PeriodicOrthocrossing
