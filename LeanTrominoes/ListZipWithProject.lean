/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Zip

/-! # Projecting aligned two-list zips -/

namespace List

theorem zipWith_project_left_of_length_eq
    {First Second Target : Type*}
    (project : First → Target) (firsts : List First) (seconds : List Second)
    (lengthEq : firsts.length = seconds.length) :
    List.zipWith (fun first _second => project first) firsts seconds =
      firsts.map project := by
  induction firsts generalizing seconds with
  | nil =>
      have secondsNil : seconds = [] :=
        List.eq_nil_of_length_eq_zero lengthEq.symm
      subst seconds
      rfl
  | cons first firsts induction =>
      cases seconds with
      | nil => simp at lengthEq
      | cons second seconds =>
          simp only [List.zipWith_cons_cons, List.map_cons]
          rw [induction seconds (Nat.succ.inj lengthEq)]

theorem zipWith_project_right_of_length_eq
    {First Second Target : Type*}
    (project : Second → Target) (firsts : List First) (seconds : List Second)
    (lengthEq : firsts.length = seconds.length) :
    List.zipWith (fun _first second => project second) firsts seconds =
      seconds.map project := by
  induction firsts generalizing seconds with
  | nil =>
      have secondsNil : seconds = [] :=
        List.eq_nil_of_length_eq_zero lengthEq.symm
      subst seconds
      rfl
  | cons first firsts induction =>
      cases seconds with
      | nil => simp at lengthEq
      | cons second seconds =>
          simp only [List.zipWith_cons_cons, List.map_cons]
          rw [induction seconds (Nat.succ.inj lengthEq)]

end List
