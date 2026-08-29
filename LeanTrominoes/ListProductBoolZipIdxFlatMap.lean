/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.GetD

/-! # Flattening a Boolean product with global indices -/

namespace LeanTrominoes
namespace ListProductBoolZipIdxFlatMap

/-- Two emitted entries for each side of a Boolean product regroup into one
four-entry block per original value. The global indices are irrelevant to
the emitter and may begin anywhere. -/
theorem pair_eq_block
    {Value Output : Type}
    (values : List Value)
    (start : Nat)
    (emit : (Value × Bool) → Nat → Output) :
    (((values.product [true, false]).zipIdx start).flatMap fun tagged =>
        [emit tagged.1 0, emit tagged.1 1]) =
      values.flatMap fun value =>
        [emit (value, true) 0, emit (value, true) 1,
          emit (value, false) 0, emit (value, false) 1] := by
  induction values generalizing start with
  | nil => rfl
  | cons value values induction =>
      simp [List.product, Nat.add_assoc]
      exact induction (start + 2)

end ListProductBoolZipIdxFlatMap
end LeanTrominoes
