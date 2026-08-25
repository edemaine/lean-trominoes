/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Batteries.Data.List.Lemmas

/-! # Pointwise maps aligned with presentation indices -/

namespace LeanTrominoes.List

universe u v w x

theorem zipWith_map_zipIdx
    {Value : Type u} {FirstType : Type v} {SecondType : Type w}
    {OutputType : Type x}
    (operation : FirstType → SecondType → OutputType)
    (first : Value → FirstType)
    (second : Value × Nat → SecondType)
    (values : List Value) (start : Nat) :
    List.zipWith operation (values.map first)
        ((values.zipIdx start).map second) =
      (values.zipIdx start).map fun entry =>
        operation (first entry.1) (second entry) := by
  induction values generalizing start with
  | nil => rfl
  | cons value values induction =>
      simp [List.zipIdx_cons, induction]

end LeanTrominoes.List
