/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Card

/-! # A bounded-witness characterization of degree two or three -/
namespace LeanTrominoes

theorem finset_card_two_or_three_iff {A : Type} [DecidableEq A] (s : Finset A) :
    (s.card = 2 ∨ s.card = 3) ↔
      ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ ∀ x ∈ s, x = a ∨ x = b ∨ x = c := by
  constructor
  · rintro (h | h)
    · obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp h
      refine ⟨a,by simp,b,by simp,b,by simp,hab,?_⟩
      intro x hx
      simpa only [Finset.mem_insert,Finset.mem_singleton,or_self] using hx
    · obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp h
      refine ⟨a,by simp,b,by simp,c,by simp,hab,?_⟩
      intro x hx
      simpa only [Finset.mem_insert,Finset.mem_singleton,or_self] using hx
  · rintro ⟨a,ha,b,hb,c,hc,hab,cover⟩
    have lower : ({a,b} : Finset A) ⊆ s := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have upper : s ⊆ ({a,b,c} : Finset A) := by
      intro x hx
      simpa only [Finset.mem_insert,Finset.mem_singleton] using cover x hx
    have lo := Finset.card_le_card lower
    have hi := Finset.card_le_card upper
    have small : ({a,b,c} : Finset A).card ≤ 3 := by
      have h := Finset.card_insert_le a ({b,c} : Finset A)
      have k := Finset.card_insert_le b ({c} : Finset A)
      simp only [Finset.card_singleton] at k
      omega
    rw [Finset.card_pair hab] at lo
    omega

end LeanTrominoes
