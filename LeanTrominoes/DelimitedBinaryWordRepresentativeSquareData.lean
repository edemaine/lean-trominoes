/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordEqualitySquareData
import LeanTrominoes.LastRepresentativeEqualityRows

/-! # Last representatives of square binary-word equality rows -/

namespace LeanTrominoes.DelimitedBinaryWordRepresentativeSquare

/-- Equality rows at the last presentation occurrence of each binary word. -/
def rows (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  LastRepresentativeEqualityRows.rows
    (DelimitedBinaryWordEqualitySquare.rows input)

end LeanTrominoes.DelimitedBinaryWordRepresentativeSquare
