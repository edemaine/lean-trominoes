/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Zip

/-! # Flattening four-list zips over an aligned first column -/

namespace List

/-- Pointwise-related first columns may be substituted while flattening a
four-column zip, when the block equality drops the middle two columns. -/
theorem zipWith4_flatten_eq_zipWith_flatten_of_forall₂
    {First Second Third Fourth Fifth Element : Type*}
    (relation : First → Second → Prop)
    (left : First → Third → Fourth → Fifth → List Element)
    (right : Second → Fifth → List Element)
    {firsts : List First} {seconds : List Second}
    (aligned : List.Forall₂ relation firsts seconds)
    (thirds : List Third) (fourths : List Fourth) (fifths : List Fifth)
    (firstThirdLength : firsts.length = thirds.length)
    (firstFourthLength : firsts.length = fourths.length)
    (firstFifthLength : firsts.length = fifths.length)
    (blockEq : ∀ first second third fourth fifth,
      relation first second →
        left first third fourth fifth = right second fifth) :
    (List.zipWith4 left firsts thirds fourths fifths).flatten =
      (List.zipWith right seconds fifths).flatten := by
  induction aligned generalizing thirds fourths fifths with
  | nil =>
      have thirdsNil : thirds = [] :=
        List.eq_nil_of_length_eq_zero firstThirdLength.symm
      have fourthsNil : fourths = [] :=
        List.eq_nil_of_length_eq_zero firstFourthLength.symm
      have fifthsNil : fifths = [] :=
        List.eq_nil_of_length_eq_zero firstFifthLength.symm
      subst thirds
      subst fourths
      subst fifths
      rfl
  | @cons first second firsts seconds head tail induction =>
      cases thirds with
      | nil => simp at firstThirdLength
      | cons third thirds =>
          cases fourths with
          | nil => simp at firstFourthLength
          | cons fourth fourths =>
              cases fifths with
              | nil => simp at firstFifthLength
              | cons fifth fifths =>
                  simp only [List.zipWith4, List.zipWith_cons_cons,
                    List.flatten_cons]
                  rw [blockEq first second third fourth fifth head]
                  rw [induction thirds fourths fifths
                    (Nat.succ.inj firstThirdLength)
                    (Nat.succ.inj firstFourthLength)
                    (Nat.succ.inj firstFifthLength)]

end List
