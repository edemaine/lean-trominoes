/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ListLastOccurrenceEntries

/-! # Recovering list indices by counting earlier sorted addresses -/
namespace LeanTrominoes.SortedAddressRank
variable {α : Type}

theorem before_get_length (entries : List (Nat × α))
    (sorted : (entries.map Prod.fst).SortedLT) (i : Nat) (hi : i<entries.length) :
    (entries.filter (fun e => decide (e.1 < entries[i].1))).length = i := by
  induction entries generalizing i with
  | nil => simp at hi
  | cons first rest ih =>
    have h := sorted.pairwise
    simp only [List.map_cons,List.pairwise_cons] at h
    have later (e : Nat × α) (he : e∈rest) : first.1<e.1 :=
      h.1 e.1 (List.mem_map.mpr ⟨e,he,rfl⟩)
    cases i with
    | zero =>
      have empty : rest.filter (fun e => decide (e.1<first.1)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro e he
        have hl := later e he
        simp only [decide_eq_true_eq]
        omega
      change (List.filter (fun e => decide (e.1<first.1)) (first::rest)).length = 0
      rw [List.filter_cons]
      simp only [lt_self_iff_false,decide_false,Bool.false_eq_true,if_false,empty,List.length_nil]
    | succ i =>
      have hi' : i<rest.length := by simpa using hi
      have earlier := later rest[i] (List.getElem_mem hi')
      have tail := ih (List.sortedLT_iff_pairwise.mpr h.2) i hi'
      change (List.filter (fun e => decide (e.1<rest[i].1)) (first::rest)).length = i+1
      rw [List.filter_cons]
      simp only [earlier,decide_true,if_true,List.length_cons]
      exact congrArg Nat.succ tail

theorem idxOf_eq_before [DecidableEq α] (entries : List (Nat × α))
    (sorted : (entries.map Prod.fst).SortedLT) (distinct : (entries.map Prod.snd).Nodup)
    (p : Nat) (a : α) (member : (p,a) ∈ entries) :
    (entries.map Prod.snd).idxOf a = (entries.filter fun e => decide (e.1<p)).length := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp member
  have rank := before_get_length entries sorted i hi
  rw [eq] at rank
  rw [rank]
  have atIndex : (entries.map Prod.snd)[i]'(by simpa using hi) = a := by simp [eq]
  rw [← atIndex]
  exact distinct.idxOf_getElem i (by simpa using hi)

end LeanTrominoes.SortedAddressRank
