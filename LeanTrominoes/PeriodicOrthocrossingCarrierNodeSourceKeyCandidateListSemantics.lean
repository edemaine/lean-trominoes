/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCandidatePairSemantics

/-! # Semantics of padded carrier-node source-key pair lists -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNodeSourceKeyCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem guardedPairMergedWords_componentPairs
    (candidates : List (Candidate CarrierNode)) :
    DelimitedBinaryWordGuardedPairMerge.mergedWords
        (componentPairs candidates) =
      mergedWords candidates := by
  apply congrArg DelimitedBinaryWords.Input.mk
  unfold componentPairs
  rw [List.map_map]
  apply List.map_congr_left
  intro candidate _candidateMember
  exact mergePair_componentPair candidate

end CarrierNodeSourceKeyCandidateWords
end LeanTrominoes.PeriodicOrthocrossing
