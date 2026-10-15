/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Card

/-! # A bounded universal test for a three-element list -/
namespace LeanTrominoes

theorem list_length_le_three_iff {α : Type*} [DecidableEq α]
    (xs : List α) (distinct : xs.Nodup) :
    xs.length ≤ 3 ↔ ∀ a ∈ xs, ∀ b ∈ xs, ∀ c ∈ xs, ∀ d ∈ xs,
      a=b ∨ a=c ∨ a=d ∨ b=c ∨ b=d ∨ c=d := by
  constructor
  · intro bound a ha b hb c hc d hd
    by_contra h
    push_neg at h
    have subset : ({a,b,c,d} : Finset α) ⊆ xs.toFinset := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp_all
    have card := (Finset.card_le_card subset).trans (List.toFinset_card_le xs)
    simp only [Finset.card_insert_of_notMem,Finset.mem_insert,Finset.mem_singleton,
      h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2,
      or_self,not_false_eq_true,Finset.card_singleton] at card
    omega
  · intro check
    rcases xs with _ | ⟨a,xs⟩
    · simp
    rcases xs with _ | ⟨b,xs⟩
    · simp
    rcases xs with _ | ⟨c,xs⟩
    · simp
    rcases xs with _ | ⟨d,xs⟩
    · simp
    have four := check a (by simp) b (by simp) c (by simp) d (by simp)
    simp only [List.nodup_cons,List.mem_cons,not_or] at distinct
    rcases four with h | h | h | h | h | h <;> simp_all

end LeanTrominoes
