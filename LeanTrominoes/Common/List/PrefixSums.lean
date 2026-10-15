/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

/-! # Stable prefix sums -/

namespace LeanTrominoes
namespace PrefixSums

/-- The starting offsets of a list of consecutive blocks, given an initial offset. -/
def startsAux : Nat → List Nat → List Nat
  | _, [] => []
  | start, value :: values =>
      start :: startsAux (start + value) values

/-- The starting offsets of consecutive blocks with the given sizes. -/
def starts (values : List Nat) : List Nat := startsAux 0 values

@[simp] theorem startsAux_nil (start : Nat) :
    startsAux start [] = [] := rfl

@[simp] theorem startsAux_cons (start value : Nat) (values : List Nat) :
    startsAux start (value :: values) =
      start :: startsAux (start + value) values := rfl

@[simp] theorem starts_nil : starts [] = [] := rfl

@[simp] theorem starts_cons (value : Nat) (values : List Nat) :
    starts (value :: values) =
      0 :: startsAux value values := by
  simp [starts]

@[simp] theorem startsAux_length (start : Nat) (values : List Nat) :
    (startsAux start values).length = values.length := by
  induction values generalizing start with
  | nil => rfl
  | cons value values induction =>
      simp [startsAux, induction]

@[simp] theorem starts_length (values : List Nat) :
    (starts values).length = values.length := by
  simp [starts]

end PrefixSums
end LeanTrominoes
