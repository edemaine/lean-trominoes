/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Enum

/-! # Alternating Boolean labels on flattened blocks -/

namespace LeanTrominoes.AlternatingBlockAxes

/-- Label every element of successive blocks by alternating true and false. -/
def axes {Value : Type*} (blocks : List (List Value)) : List Bool :=
  (blocks.zipIdx 0).flatMap fun tagged =>
    List.replicate tagged.1.length (decide (tagged.2 % 2 = 0))

private theorem axes_length_aux
    {Value : Type*} (blocks : List (List Value)) (start : Nat) :
    ((blocks.zipIdx start).flatMap fun tagged =>
      List.replicate tagged.1.length
        (decide (tagged.2 % 2 = 0))).length =
        blocks.flatten.length := by
  induction blocks generalizing start with
  | nil => rfl
  | cons block blocks induction =>
      simp only [List.zipIdx_cons, List.flatMap_cons,
        List.length_append, List.length_replicate, List.flatten_cons]
      rw [induction (start + 1)]

@[simp] theorem axes_length {Value : Type*}
    (blocks : List (List Value)) :
    (axes blocks).length = blocks.flatten.length := by
  unfold axes
  exact axes_length_aux blocks 0

end LeanTrominoes.AlternatingBlockAxes
