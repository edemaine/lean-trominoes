/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.ListZipWithFourProjection
import Mathlib.Data.List.Forall2

/-! # Mapping and aligning four-column list zips -/

namespace List

/-- Mapping a four-column zip only changes its combining function. -/
theorem map_zipWith4
    {First Second Third Fourth Middle Target : Type*}
    (transform : Middle → Target)
    (combine : First → Second → Third → Fourth → Middle) :
    ∀ (first : List First) (second : List Second)
      (third : List Third) (fourth : List Fourth),
      (zipWith4 combine first second third fourth).map transform =
        zipWith4 (fun a b c d => transform (combine a b c d)) first second third fourth
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, [], _ => rfl
  | _ :: _, _ :: _, _ :: _, [] => rfl
  | a :: first, b :: second, c :: third, d :: fourth => by
      simp only [zipWith4, map_cons]
      rw [map_zipWith4 transform combine first second third fourth]

/-- Two mapped source columns remain aligned with their common source list
when the other two columns have that same length. -/
theorem forall₂_zipWith4_maps
    {First Entry Second Third Fourth Target : Type*}
    (combine : First → Second → Third → Fourth → Target)
    (second : Entry → Second) (fourth : Entry → Fourth)
    (relation : Target → Entry → Prop)
    (pointwise : ∀ first entry third,
      relation (combine first (second entry) third (fourth entry)) entry)
    (first : List First) (entries : List Entry) (third : List Third)
    (firstLength : first.length = entries.length)
    (thirdLength : third.length = entries.length) :
    Forall₂ relation (zipWith4 combine first (entries.map second) third (entries.map fourth)) entries := by
  induction entries generalizing first third with
  | nil =>
      have firstNil : first = [] := length_eq_zero_iff.mp firstLength
      subst first
      exact .nil
  | cons entry entries induction =>
      cases first with
      | nil => simp at firstLength
      | cons first firsts =>
          cases third with
          | nil => simp at thirdLength
          | cons third thirds =>
              change Forall₂ relation
                (combine first (second entry) third (fourth entry) ::
                  zipWith4 combine firsts (entries.map second) thirds (entries.map fourth))
                (entry :: entries)
              exact .cons (pointwise first entry third)
                (induction firsts thirds (Nat.succ.inj firstLength) (Nat.succ.inj thirdLength))

/-- Strengthen an alignment using facts about membership in both lists. -/
theorem Forall₂.imp_of_mem
    {First Second : Type*} {relation result : First → Second → Prop}
    {first : List First} {second : List Second}
    (aligned : Forall₂ relation first second) :
    (∀ a ∈ first, ∀ b ∈ second, relation a b → result a b) →
      Forall₂ result first second := by
  induction aligned with
  | nil => intro _; exact .nil
  | @cons a b first second related aligned induction =>
      intro property
      exact .cons (property a (by simp) b (by simp) related)
        (induction fun x xMember y yMember relation =>
          property x (mem_cons_of_mem a xMember) y (mem_cons_of_mem b yMember) relation)

/-- Pointwise aligned images give equal mapped lists. -/
theorem map_eq_map_of_forall₂
    {First Second Target : Type*}
    (first : First → Target) (second : Second → Target)
    {firsts : List First} {seconds : List Second}
    (aligned : Forall₂ (fun a b => first a = second b) firsts seconds) :
    firsts.map first = seconds.map second := by
  induction aligned with
  | nil => rfl
  | cons head _ induction =>
      simp only [List.map_cons]
      rw [head, induction]

end List
