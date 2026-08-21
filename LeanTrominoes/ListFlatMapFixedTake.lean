/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Taking fixed-width flat-map prefixes -/

namespace LeanTrominoes
namespace List

/-- A prefix ending on a fixed-width block boundary is exactly the flat map
of the corresponding outer prefix. -/
theorem take_mul_flatMap_of_length_eq
    {Value Output : Type*}
    (values : List Value) (block : Value → List Output) (width count : Nat)
    (blockLength : ∀ value, (block value).length = width) :
    (values.flatMap block).take (width * count) =
      (values.take count).flatMap block := by
  induction count generalizing values with
  | zero => simp
  | succ count induction =>
      cases values with
      | nil => simp
      | cons value values =>
          simp only [List.flatMap_cons, List.take_succ_cons]
          rw [show width * (count + 1) =
              (block value).length + width * count by
                rw [blockLength, Nat.mul_succ, Nat.add_comm],
            List.take_length_add_append,
            induction]

end List
end LeanTrominoes
