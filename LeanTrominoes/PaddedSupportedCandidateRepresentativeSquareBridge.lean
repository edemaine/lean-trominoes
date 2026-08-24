/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordRepresentativeSquareSemantics
import LeanTrominoes.DelimitedBinaryWordsDropLastData
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowData

/-! # Bridge from generic word squares to guarded candidates -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*}

/-- Running the generic representative-square construction on guarded words
with their appended sentinel gives the candidate-specific raw rows. -/
theorem representativeSquareRows_eq_withSentinel
    (encodeValue : Value → List Bool)
    (candidates : List (Candidate Value)) :
    DelimitedBinaryWordRepresentativeSquare.rows
        (wordsWithSentinel encodeValue candidates) =
      representativeRowsWithSentinel encodeValue candidates := by
  rw [DelimitedBinaryWordRepresentativeSquare.rows_eq]
  rfl

/-- Dropping the generic square's final representative row gives exactly the
candidate-specific sentinel-free representative rows. -/
theorem dropLast_representativeSquareRows_eq
    (encodeValue : Value → List Bool)
    (candidates : List (Candidate Value)) :
    DelimitedBinaryWordsDropLastMachine.dropLast
        (DelimitedBinaryWordRepresentativeSquare.rows
          (wordsWithSentinel encodeValue candidates)) =
      representativeRows encodeValue candidates := by
  rw [representativeSquareRows_eq_withSentinel]
  rfl

end LeanTrominoes.PaddedSupportedCandidateWords
