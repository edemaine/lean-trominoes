/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordEqualitySquareSemantics
import LeanTrominoes.DelimitedBinaryWordRepresentativeSquareData

/-! # Semantics of last representatives of binary-word squares -/

namespace LeanTrominoes.DelimitedBinaryWordRepresentativeSquare

/-- The generic machine-oriented row construction is exactly semantic
last-occurrence selection over the input words' equality rows. -/
theorem rows_eq (input : DelimitedBinaryWords.Input) :
    rows input =
      LastRepresentativeEqualityRows.rows
        ⟨LastRepresentativeEqualityRows.equalityRows input.words⟩ := by
  unfold rows
  rw [DelimitedBinaryWordEqualitySquare.rows_eq]

end LeanTrominoes.DelimitedBinaryWordRepresentativeSquare
