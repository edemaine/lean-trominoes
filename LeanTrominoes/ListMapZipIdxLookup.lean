/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Basic

/-! # Lookup through an indexed list map -/

namespace LeanTrominoes
namespace IndexedListScan

/-- Mapping over `zipIdx` preserves a successful lookup and supplies the
looked-up element's stable index. -/
theorem map_zipIdx_getElem?_eq_some
    {Value Output : Type}
    (values : List Value)
    (output : Value × Nat → Output)
    (value : Value)
    (index : Nat)
    (lookup : values[index]? = some value) :
    (values.zipIdx.map output)[index]? =
      some (output (value, index)) := by
  rw [List.getElem?_map, List.getElem?_zipIdx, lookup]
  simp only [Option.map_some, Nat.zero_add]

end IndexedListScan
end LeanTrominoes
