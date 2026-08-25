/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCounts

/-! # Indexed semantics of row-prefix true counts -/

namespace LeanTrominoes.DelimitedBinaryWordPrefixTrueCounts

theorem countsAux_map
    {Value : Type*} (values : List Value) (row : Value → List Bool)
    (start : Nat) :
    countsAux start (values.map row) =
      (values.zipIdx start).map fun entry =>
        count entry.2 (row entry.1) := by
  induction values generalizing start with
  | nil => rfl
  | cons value values induction =>
      simp [List.zipIdx_cons, induction]

end LeanTrominoes.DelimitedBinaryWordPrefixTrueCounts
