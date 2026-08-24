/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFields

/-! # Length of fixed-axis value streams -/

namespace LeanTrominoes.FixedAxisUnaryFields

theorem values_length_of_length_eq (axes actives : List Bool)
    (lengthEq : actives.length = axes.length) :
    (values axes actives).length = axes.length := by
  unfold values
  rw [List.length_zipWith, lengthEq, Nat.min_self]

end LeanTrominoes.FixedAxisUnaryFields
