/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Flattened lengths of pointwise-related block lists -/

namespace List.Forall₂

private theorem related_length_eq
    {First Second : Type*} {Relation : First → Second → Prop}
    {first : List First} {second : List Second}
    (related : List.Forall₂ Relation first second) :
    first.length = second.length := by
  induction related with
  | nil => rfl
  | cons _ _ induction => simp [induction]

theorem flatten_length_eq
    {First Second : Type*} {Relation : First → Second → Prop}
    {first : List (List First)} {second : List (List Second)}
    (related : List.Forall₂ (List.Forall₂ Relation) first second) :
    first.flatten.length = second.flatten.length := by
  induction related with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.flatten_cons, List.length_append]
      rw [related_length_eq head, induction]

end List.Forall₂
