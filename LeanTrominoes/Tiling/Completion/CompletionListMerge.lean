import Mathlib.Data.List.Perm.Basic

/-! Structurally recursive sorting for kernel-checked cell certificates.
Every fuel value preserves the input multiset; a checked output certifies
both that the chosen fuel suffices and that the resulting order is correct. -/

namespace LeanTrominoes.CompletionListMerge

def merge {α : Type} (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | n + 1, x :: xs, y :: ys =>
    if le x y then x :: merge le n xs (y :: ys)
    else y :: merge le n (x :: xs) ys

theorem merge_perm {α : Type} (le : α → α → Bool) (n : Nat) (xs ys : List α) :
    (merge le n xs ys).Perm (xs ++ ys) := by
  induction n generalizing xs ys with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    cases xs with
    | nil => simp [merge]
    | cons x xs =>
      cases ys with
      | nil => simp [merge]
      | cons y ys =>
        simp only [merge]
        split
        · exact (ih xs (y :: ys)).cons x
        · exact ((ih (x :: xs) ys).cons y).trans List.perm_middle.symm

def sort {α : Type} (le : α → α → Bool) : Nat → List α → List α
  | 0, xs => xs
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | n + 1, x :: y :: xs =>
    let all := x :: y :: xs
    merge le all.length (sort le n (all.take (all.length / 2)))
      (sort le n (all.drop (all.length / 2)))

theorem sort_perm {α : Type} (le : α → α → Bool) (n : Nat) (xs : List α) :
    (sort le n xs).Perm xs := by
  induction n generalizing xs with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    cases xs with
    | nil => exact List.Perm.refl _
    | cons x xs =>
      cases xs with
      | nil => exact List.Perm.refl _
      | cons y xs =>
        dsimp only [sort]
        exact (merge_perm _ _ _ _).trans (((ih _).append (ih _)).trans (by
          rw [List.take_append_drop]))

end LeanTrominoes.CompletionListMerge
