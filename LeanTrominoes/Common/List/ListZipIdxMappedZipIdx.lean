/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Enum

/-! # Re-indexing pointwise indexed maps -/

namespace List

/-- Mapping an already indexed list and indexing the result again preserves
the original numeric index. -/
theorem zipIdx_map_zipIdx
    {Value Output : Type}
    (values : List Value) (mapped : Value × Nat → Output) :
    (values.zipIdx.map mapped).zipIdx =
      values.zipIdx.map fun tagged => (mapped tagged, tagged.2) := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simp

end List
