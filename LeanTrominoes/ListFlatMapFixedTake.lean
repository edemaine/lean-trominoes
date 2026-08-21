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

/-- At a known outer entry, a prefix that continues partway into its fixed
block consists of every earlier block followed by that local block prefix. -/
theorem take_mul_add_flatMap_of_getElem?
    {Value Output : Type*}
    (values : List Value) (block : Value → List Output) (width : Nat)
    (blockLength : ∀ value, (block value).length = width)
    (value : Value) (index offset : Nat)
    (lookup : values[index]? = some value) (offsetLe : offset ≤ width) :
    (values.flatMap block).take (width * index + offset) =
      (values.take index).flatMap block ++ (block value).take offset := by
  induction values generalizing value index with
  | nil => simp at lookup
  | cons head tail induction =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
          subst value
          simp only [Nat.mul_zero, Nat.zero_add, List.flatMap_cons,
            List.take_zero, List.flatMap_nil, List.nil_append]
          exact List.take_append_of_le_length
            (by rw [blockLength]; exact offsetLe)
      | succ index =>
          simp only [List.getElem?_cons_succ] at lookup
          simp only [List.flatMap_cons, List.take_succ_cons]
          rw [show width * (index + 1) + offset =
              (block head).length + (width * index + offset) by
                rw [blockLength, Nat.mul_succ]
                omega,
            List.take_length_add_append,
            induction value index lookup]
          simp only [List.append_assoc]

end List
end LeanTrominoes
