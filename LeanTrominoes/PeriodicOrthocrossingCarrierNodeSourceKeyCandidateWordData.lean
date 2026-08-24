/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeData
import LeanTrominoes.PaddedSupportedCandidateWordData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyWordData

/-! # Guarded source-key words of padded carrier-node candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNodeSourceKeyCandidateWords

open PaddedSupportedCandidateWords
open PaddedSupportedLastRepresentativeEqualityRows

/-- Replace a padded node's geometric support tag by exact slot activity and
project its active value to the compact source-key pair. -/
def sourceKeyCandidate (candidate : Candidate CarrierNode) :
    Candidate CarrierNodeSourceKeys.SourceKeyPair where
  value := candidate.value.map CarrierNodeSourceKeys.pair
  supported := candidate.value.isSome

/-- The two adjacent guarded carrier-key words emitted for one padded node
slot before the physical pair merger. -/
def componentPair (candidate : Candidate CarrierNode) :
    List Bool × List Bool :=
  match candidate.value with
  | some node =>
      let keys := CarrierNodeSourceKeys.pair node
      (true :: CarrierKeyWords.word keys.1,
        true :: CarrierKeyWords.word keys.2)
  | none => (sentinelWord, sentinelWord)

def componentPairs (candidates : List (Candidate CarrierNode)) :
    List (List Bool × List Bool) :=
  candidates.map componentPair

/-- Guarded compact source-key words in the same padded slot order. -/
def mergedWords (candidates : List (Candidate CarrierNode)) :
    DelimitedBinaryWords.Input :=
  ⟨candidates.map fun candidate =>
    guardedWord CarrierNodeSourceKeys.word
      (sourceKeyCandidate candidate)⟩

end CarrierNodeSourceKeyCandidateWords
end LeanTrominoes.PeriodicOrthocrossing
