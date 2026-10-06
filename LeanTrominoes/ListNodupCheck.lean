/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Chain

namespace LeanTrominoes

private def mergeCodes : Nat → List Nat → List Nat → List Nat
  | 0, first, second => first ++ second
  | _ + 1, [], second => second
  | _ + 1, first, [] => first
  | fuel + 1, a :: first, b :: second =>
      if a ≤ b then a :: mergeCodes fuel first (b :: second)
      else b :: mergeCodes fuel (a :: first) second

private theorem mergeCodes_perm (fuel : Nat) (first second : List Nat) :
    (mergeCodes fuel first second).Perm (first ++ second) := by
  induction fuel generalizing first second with
  | zero => rfl
  | succ fuel ih =>
    cases first with
    | nil => simp [mergeCodes]
    | cons a first =>
      cases second with
      | nil => simp [mergeCodes]
      | cons b second =>
        simp only [mergeCodes]
        split
        · exact (ih first (b :: second)).cons a
        · exact ((ih (a :: first) second).cons b).trans List.perm_middle.symm

/-- Structural fuel makes the sorting computation reducible by the kernel. -/
private def sortCodes : Nat → List Nat → List Nat
  | 0, items => items
  | fuel + 1, items =>
      if items.length ≤ 1 then items
      else
        let split := items.length / 2
        mergeCodes items.length
          (sortCodes fuel (items.take split))
          (sortCodes fuel (items.drop split))

private theorem sortCodes_perm (fuel : Nat) (items : List Nat) :
    (sortCodes fuel items).Perm items := by
  induction fuel generalizing items with
  | zero => rfl
  | succ fuel ih =>
    simp only [sortCodes]
    split
    · rfl
    · exact (mergeCodes_perm _ _ _).trans (by
        simpa only [List.take_append_drop] using (ih (items.take (items.length / 2))).append (ih (items.drop (items.length / 2))))

/-- Sort natural-number codes and check adjacent strict inequalities. -/
def listNodupCheck {α : Type*} [Encodable α] (items : List α) : Bool :=
  let codes := items.map Encodable.encode
  decide ((sortCodes codes.length codes).IsChain (· < ·))

/-- Strictly increasing sorted codes certify that the original list has no duplicates. -/
theorem listNodupCheck_sound {α : Type*} [Encodable α] (items : List α)
    (checked : listNodupCheck items = true) : items.Nodup := by
  simp only [listNodupCheck, decide_eq_true_eq] at checked
  have pairwise := List.isChain_iff_pairwise.mp checked
  have nodup : (sortCodes (items.map Encodable.encode).length
      (items.map Encodable.encode)).Nodup :=
    pairwise.imp (fun less => ne_of_lt less)
  exact List.Nodup.of_map Encodable.encode ((sortCodes_perm _ _).nodup_iff.mp nodup)

end LeanTrominoes
