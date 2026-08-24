/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRows

/-! # Prefix-supported last-representative equality rows -/

namespace LeanTrominoes.LastRepresentativeEqualityRows

/-- Whether an equality row meets a distinguished prefix of its columns. -/
def meetsPrefix (prefixLength : Nat) (row : List Bool) : Bool :=
  (row.take prefixLength).contains true

/-- Last-representative equality rows whose class occurs in the designated
prefix of the candidate stream. -/
def prefixSupportedRows (prefixLength : Nat)
    (input : DelimitedBinaryWords.Input) : DelimitedBinaryWords.Input :=
  ⟨(rows input).words.filter (meetsPrefix prefixLength)⟩

end LeanTrominoes.LastRepresentativeEqualityRows
