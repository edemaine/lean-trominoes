/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Zip

/-! # Zipping aligned flattened block families -/

namespace List

theorem zipWith_replicate_left
    {First Second Target : Type*}
    (combine : First → Second → Target) (first : First)
    (seconds : List Second) :
    List.zipWith combine (List.replicate seconds.length first) seconds =
      seconds.map (combine first) := by
  induction seconds with
  | nil => rfl
  | cons second seconds induction =>
      simp only [List.length_cons, List.replicate_succ,
        List.zipWith_cons_cons, List.map_cons]
      rw [induction]

theorem zipWith_append_of_length_eq
    {First Second Target : Type*}
    (combine : First → Second → Target)
    (firstPrefix firstSuffix : List First)
    (secondPrefix secondSuffix : List Second)
    (lengthEq : firstPrefix.length = secondPrefix.length) :
    List.zipWith combine
        (firstPrefix ++ firstSuffix) (secondPrefix ++ secondSuffix) =
      List.zipWith combine firstPrefix secondPrefix ++
        List.zipWith combine firstSuffix secondSuffix := by
  induction firstPrefix generalizing secondPrefix with
  | nil =>
      have secondNil : secondPrefix = [] :=
        List.eq_nil_of_length_eq_zero lengthEq.symm
      subst secondPrefix
      rfl
  | cons first firstPrefix induction =>
      cases secondPrefix with
      | nil => simp at lengthEq
      | cons second secondPrefix =>
          simp only [List.length_cons] at lengthEq
          simp only [List.cons_append, List.zipWith_cons_cons]
          rw [induction secondPrefix (Nat.succ.inj lengthEq)]

/-- Zipping two flattened, pointwise equally sized block families can be
performed blockwise. -/
theorem zipWith_flatMap_aligned
    {FirstSource SecondSource First Second Target : Type*}
    (combine : First → Second → Target)
    (firstBlock : FirstSource → List First)
    (secondBlock : SecondSource → List Second)
    (blockLengths : ∀ first second,
      (firstBlock first).length = (secondBlock second).length) :
    ∀ (firsts : List FirstSource) (seconds : List SecondSource),
    List.zipWith combine
        (firsts.flatMap firstBlock) (seconds.flatMap secondBlock) =
      (List.zipWith
        (fun first second =>
          List.zipWith combine (firstBlock first) (secondBlock second))
        firsts seconds).flatten
  | [], _ => rfl
  | _ :: _, [] => by simp
  | first :: firsts, second :: seconds => by
      simp only [List.flatMap_cons, List.zipWith_cons_cons,
        List.flatten_cons]
      rw [zipWith_append_of_length_eq combine
        (firstBlock first) (firsts.flatMap firstBlock)
        (secondBlock second) (seconds.flatMap secondBlock)
        (blockLengths first second),
        zipWith_flatMap_aligned combine firstBlock secondBlock
          blockLengths firsts seconds]

/-- Pointwise block permutations lift through aligned zipping and
flattening, with the expected family indexed by the first column. -/
theorem zipWith_flatten_perm_flatMap_left_of_length_eq
    {First Second Element : Type*}
    (block : First → Second → List Element)
    (expected : First → List Element)
    (pointwise : ∀ first second, (block first second).Perm (expected first)) :
    ∀ (firsts : List First) (seconds : List Second),
      firsts.length = seconds.length →
      (List.zipWith block firsts seconds).flatten.Perm
        (firsts.flatMap expected)
  | [], [], _ => List.Perm.nil
  | [], _ :: _, lengthEq => by simp at lengthEq
  | _ :: _, [], lengthEq => by simp at lengthEq
  | first :: firsts, second :: seconds, lengthEq => by
      simp only [List.length_cons] at lengthEq
      simp only [List.zipWith_cons_cons, List.flatten_cons,
        List.flatMap_cons]
      exact List.Perm.append (pointwise first second)
        (zipWith_flatten_perm_flatMap_left_of_length_eq
          block expected pointwise firsts seconds
          (Nat.succ.inj lengthEq))

end List
