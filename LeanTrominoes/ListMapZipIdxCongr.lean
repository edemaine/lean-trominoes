/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Enum

/-! # Congruence for indexed list maps -/

namespace List

theorem map_zipIdx_eq_map_of_mem {Value Output : Type}
    (values : List Value) (indexed : Value × Nat → Output)
    (plain : Value → Output)
    (equal : ∀ tagged ∈ values.zipIdx,
      indexed tagged = plain tagged.1) :
    values.zipIdx.map indexed = values.map plain := by
  conv_rhs =>
    rw [← List.zipIdx_map_fst 0 values, List.map_map]
  exact List.map_congr_left equal

end List
