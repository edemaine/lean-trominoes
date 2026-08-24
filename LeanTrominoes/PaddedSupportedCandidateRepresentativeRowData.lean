/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateEqualityRowData

/-! # Representative rows of guarded padded-candidate words -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*}

/-- Last-occurrence representatives of the complete guarded-word equality
matrix.  This raw output still contains the final sentinel row. -/
def representativeRowsWithSentinel (encodeValue : Value → List Bool)
    (candidates : List (Candidate Value)) : DelimitedBinaryWords.Input :=
  LastRepresentativeEqualityRows.rows
    ⟨equalityRowsWithSentinel encodeValue candidates⟩

/-- The guarded-word representatives after removing the one known final
sentinel row. -/
def representativeRows (encodeValue : Value → List Bool)
    (candidates : List (Candidate Value)) : DelimitedBinaryWords.Input :=
  ⟨(representativeRowsWithSentinel encodeValue candidates).words.dropLast⟩

end LeanTrominoes.PaddedSupportedCandidateWords
