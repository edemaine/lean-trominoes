/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.GetD

/-! # Indexing through a finite range -/

namespace List

/-- Looking up a valid range entry and using it as another index preserves
the original index. -/
theorem getD_range_getD {Value : Type*}
    (values : List Value) (default : Value)
    (size index : Nat) (indexLt : index < size) :
    values.getD ((List.range size).getD index 0) default =
      values.getD index default := by
  have rangeEq : (List.range size).getD index 0 = index := by
    rw [List.getD_eq_getElem _ _ (by simpa using indexLt)]
    simp
  rw [rangeEq]

end List
