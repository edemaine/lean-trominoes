/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PrefixSums

/-! # Indexed semantics of stable prefix sums -/

namespace LeanTrominoes
namespace PrefixSums

theorem startsAux_getElem (start : Nat) (values : List Nat)
    (index : Nat) (indexLt : index < values.length) :
    (startsAux start values)[index]'(by simpa using indexLt) =
      start + (values.take index).sum := by
  induction values generalizing start index with
  | nil => simp at indexLt
  | cons value values induction =>
      cases index with
      | zero => simp [startsAux]
      | succ index =>
          simp only [startsAux, List.getElem_cons_succ,
            List.take_succ_cons, List.sum_cons]
          rw [induction (start + value) index (by simpa using indexLt)]
          omega

theorem starts_getElem (values : List Nat) (index : Nat)
    (indexLt : index < values.length) :
    (starts values)[index]'(by simpa using indexLt) =
      (values.take index).sum := by
  simpa [starts] using startsAux_getElem 0 values index indexLt

end PrefixSums
end LeanTrominoes
