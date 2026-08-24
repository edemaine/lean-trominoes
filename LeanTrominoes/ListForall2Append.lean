/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Appending pointwise-related lists -/

namespace List.Forall₂

variable {First Second : Type*}
variable {relation : First → Second → Prop}
variable {firsts remainingFirsts : List First}
variable {seconds remainingSeconds : List Second}

theorem append
    (first : List.Forall₂ relation firsts seconds)
    (second : List.Forall₂ relation remainingFirsts remainingSeconds) :
    List.Forall₂ relation
      (firsts ++ remainingFirsts) (seconds ++ remainingSeconds) := by
  induction first with
  | nil => exact second
  | cons head tail induction =>
      exact List.Forall₂.cons head induction

end List.Forall₂
