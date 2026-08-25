/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCandidateWordData

/-! # Length of compact source-key component pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Every padded carrier-node candidate contributes exactly two adjacent
guarded source-key component words. -/
theorem sourceKeyComponentWords_length
    (candidates : List
      (PaddedSupportedLastRepresentativeEqualityRows.Candidate CarrierNode)) :
    (DelimitedBinaryWordGuardedPairMerge.componentWords
      (CarrierNodeSourceKeyCandidateWords.componentPairs candidates)).words.length =
      2 * candidates.length := by
  unfold DelimitedBinaryWordGuardedPairMerge.componentWords
    CarrierNodeSourceKeyCandidateWords.componentPairs
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      simp only [List.map_cons, List.flatMap_cons, List.length_append,
        List.length_cons, List.length_nil]
      rw [induction]
      omega

end LeanTrominoes.PeriodicOrthocrossing
