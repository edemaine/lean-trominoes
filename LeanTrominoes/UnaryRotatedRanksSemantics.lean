/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryRotatedRanksInput

/-! # Semantics of aligned unary rank rotation -/

namespace LeanTrominoes
namespace UnaryRotatedRanksMachine

/-- On aligned promised inputs, rank rotation acts pointwise. -/
theorem rotatedRanks_eq_zipWith {ranks sizes : List Nat}
    (valid : Valid ranks sizes) :
    rotatedRanks ranks sizes = List.zipWith rotatedRank ranks sizes := by
  induction valid with
  | nil => rfl
  | cons rankLtSize rest induction =>
      simp only [rotatedRanks, List.zipWith_cons_cons, induction]

@[simp] theorem rotatedRanks_length {ranks sizes : List Nat}
    (valid : Valid ranks sizes) :
    (rotatedRanks ranks sizes).length = ranks.length := by
  rw [rotatedRanks_eq_zipWith valid, List.length_zipWith,
    valid.length_eq, min_self]

end UnaryRotatedRanksMachine
end LeanTrominoes
