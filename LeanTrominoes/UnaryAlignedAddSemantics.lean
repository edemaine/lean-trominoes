/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddInput

/-! # Semantics of aligned unary addition -/

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

/-- On aligned promised inputs, `sums` is ordinary pointwise addition. -/
theorem sums_eq_zipWith {firsts seconds : List Nat}
    (valid : Valid firsts seconds) :
    sums firsts seconds = List.zipWith (· + ·) firsts seconds := by
  induction valid with
  | nil => rfl
  | cons rest induction =>
      simp only [sums, List.zipWith_cons_cons, induction]

@[simp] theorem sums_length {firsts seconds : List Nat}
    (valid : Valid firsts seconds) :
    (sums firsts seconds).length = firsts.length := by
  rw [sums_eq_zipWith valid, List.length_zipWith,
    valid.length_eq, min_self]

end UnaryAlignedAddMachine
end LeanTrominoes
