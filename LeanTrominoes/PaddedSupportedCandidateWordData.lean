/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

/-! # Guarded binary words for padded supported candidates -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*}

/-- A supported active candidate receives a tagged encoding of its value.
Every other candidate receives one common rejection sentinel. -/
def guardedWord (encodeValue : Value → List Bool)
    (candidate : Candidate Value) : List Bool :=
  match candidate.supported, candidate.value with
  | true, some value => true :: encodeValue value
  | _, _ => [false]

/-- The common word used by inactive or unsupported candidates. -/
def sentinelWord : List Bool :=
  [false]

/-- Guarded candidate words followed by one explicit rejection sentinel.
The sentinel supplies the final rejection column after squaring the words. -/
def wordsWithSentinel (encodeValue : Value → List Bool)
    (candidates : List (Candidate Value)) : DelimitedBinaryWords.Input :=
  ⟨candidates.map (guardedWord encodeValue) ++ [sentinelWord]⟩

@[simp] theorem wordsWithSentinel_length
    (encodeValue : Value → List Bool)
    (candidates : List (Candidate Value)) :
    (wordsWithSentinel encodeValue candidates).words.length =
      candidates.length + 1 := by
  simp [wordsWithSentinel]

end LeanTrominoes.PaddedSupportedCandidateWords
