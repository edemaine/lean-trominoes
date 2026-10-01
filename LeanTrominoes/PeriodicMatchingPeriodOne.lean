/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicMatchingHall

/-! # Theorem 4.6: period-one perfect matchings

A finite quotient matching selects one protoedge at each left protovertex.
Translate those selected edges throughout the lattice. Bijectivity of the
quotient matching makes the lifted edges disjoint and covers both colors.
Together with the Hall descent, this proves the result for all dimensions
and arbitrary finite offsets.
-/
namespace LeanTrominoes.PeriodicBipartite
variable {L R : Type*} {d : Nat}

/-- Lift a quotient bijection using one offset at each left protovertex. -/
def lift (f : L ≃ R) (offset : L → Lattice d) :
    (L × Lattice d) ≃ (R × Lattice d) where
  toFun u := (f u.1,u.2+offset u.1)
  invFun v := (f.symm v.1,v.2-offset (f.symm v.1))
  left_inv u := by simp
  right_inv v := by simp

theorem lift_translation (f : L ≃ R) (offset : L → Lattice d) :
    TranslationInvariant (lift f offset) := by
  intro l z t
  apply Prod.ext
  · rfl
  · change z+t+offset l=z+offset l+t
    abel

theorem quotient_to_period_one (edges : List (Edge L R d)) (h : HasQuotientMatching edges) :
    HasPeriodOneMatching edges := by
  classical
  obtain ⟨f,hf⟩ := h
  choose e he hl hr using hf
  refine ⟨lift f (fun l => (e l).offset),?_,lift_translation f _⟩
  intro u
  exact ⟨e u.1,he u.1,hl u.1,hr u.1,rfl⟩

theorem period_one_to_perfect (edges : List (Edge L R d)) (h : HasPeriodOneMatching edges) :
    HasPerfectMatching edges := by
  obtain ⟨f,hf,_⟩ := h
  exact ⟨f,hf⟩

variable [Fintype L] [Fintype R]

/-- Theorem 4.6, including its finite-quotient characterization. -/
theorem perfect_iff_quotient (edges : List (Edge L R d)) :
    HasPerfectMatching edges ↔ HasQuotientMatching edges :=
  ⟨perfect_to_quotient edges,fun h => period_one_to_perfect edges (quotient_to_period_one edges h)⟩

theorem exists_period_one (edges : List (Edge L R d)) (h : HasPerfectMatching edges) :
    HasPeriodOneMatching edges := quotient_to_period_one edges (perfect_to_quotient edges h)

theorem perfect_iff_period_one (edges : List (Edge L R d)) :
    HasPerfectMatching edges ↔ HasPeriodOneMatching edges :=
  ⟨exists_period_one edges,period_one_to_perfect edges⟩

end LeanTrominoes.PeriodicBipartite
