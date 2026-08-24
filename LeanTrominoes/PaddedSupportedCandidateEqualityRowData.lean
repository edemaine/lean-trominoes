/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsSemantics
import LeanTrominoes.PaddedSupportedCandidateWordData

/-! # Equality rows of guarded padded-candidate words -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*}

/-- The complete guarded-word equality row of one candidate slot, including
its comparison with the appended rejection sentinel. -/
def equalityRowWithSentinel (encodeValue : Value → List Bool)
    (candidates : List (Candidate Value))
    (candidate : Candidate Value) : List Bool :=
  LastRepresentativeEqualityRows.equalityRow
    (wordsWithSentinel encodeValue candidates).words
    (guardedWord encodeValue candidate)

/-- The square guarded-word equality matrix, including the appended
sentinel's own final row. -/
def equalityRowsWithSentinel (encodeValue : Value → List Bool)
    (candidates : List (Candidate Value)) : List (List Bool) :=
  LastRepresentativeEqualityRows.equalityRows
    (wordsWithSentinel encodeValue candidates).words

end LeanTrominoes.PaddedSupportedCandidateWords
