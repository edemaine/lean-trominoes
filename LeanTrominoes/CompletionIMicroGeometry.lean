/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIGuardedEqBoundaryData
import Mathlib.Data.Int.Interval

/-! # The closed eighteen-by-twenty-seven microcells underlying the I-brick layout -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def microShape : Finset Cell :=
  (Finset.Ico (0 : Int) 18 ×ˢ Finset.Ico (1 : Int) 27) ∪
    (Finset.Ico (9 : Int) 18 ∪ {5}).image (fun x => (x,0)) ∪
    (Finset.Ico (0 : Int) 9 ∪ {14}).image (fun x => (x,27))

theorem micro_shape_eq : IGuardedEqBoundary.pattern.region = microShape := by decide +kernel

def MemberAt (x y : Int) : Prop :=
  (0 ≤ x ∧ x < 18 ∧ 1 ≤ y ∧ y < 27) ∨
  ((9 ≤ x ∧ x < 18 ∨ x = 5) ∧ y = 0) ∨
  ((0 ≤ x ∧ x < 9 ∨ x = 14) ∧ y = 27)

theorem mem_microShape (c : Cell) : c ∈ microShape ↔ MemberAt c.1 c.2 := by
  rcases c with ⟨x,y⟩
  simp only [microShape,Finset.mem_union,Finset.mem_product,Finset.mem_Ico,
    Finset.mem_image,Finset.mem_singleton,Prod.mk.injEq]
  unfold MemberAt
  constructor
  · intro h
    rcases h with (h | h) | h
    · exact Or.inl ⟨h.1.1,h.1.2,h.2.1,h.2.2⟩
    · obtain ⟨z,hz,eq,hy⟩ := h
      subst z
      exact Or.inr (Or.inl ⟨hz,hy.symm⟩)
    · obtain ⟨z,hz,eq,hy⟩ := h
      subst z
      exact Or.inr (Or.inr ⟨hz,hy.symm⟩)
  · intro h
    rcases h with h | h | h
    · exact Or.inl (Or.inl ⟨⟨h.1,h.2.1⟩,h.2.2⟩)
    · exact Or.inl (Or.inr ⟨x,h.1,rfl,h.2.symm⟩)
    · exact Or.inr ⟨x,h.1,rfl,h.2.symm⟩

def microOrigin (i : Cell) : Cell := (18 * i.1,27 * i.2)

def microRegion (i : Cell) : Finset Cell := IGuardedEqBoundary.pattern.region.image (Cell.add (microOrigin i))

theorem mem_microRegion (i c : Cell) :
    c ∈ microRegion i ↔ MemberAt (c.1 - 18 * i.1) (c.2 - 27 * i.2) := by
  have offset : c ∈ microRegion i ↔ Cell.sub c (microOrigin i) ∈ IGuardedEqBoundary.pattern.region := by
    constructor
    · intro hc
      obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp hc
      have cancel : Cell.sub c (microOrigin i) = d := by
        rw [← eq]
        apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
      rwa [cancel]
    · intro hc
      refine Finset.mem_image.mpr ⟨Cell.sub c (microOrigin i),hc,?_⟩
      apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
  rw [offset,micro_shape_eq,mem_microShape]
  rfl

/-- Every lattice cell belongs to at least one closed microcell. -/
theorem micro_cover (c : Cell) : ∃ i : Cell, c ∈ microRegion i := by
  by_cases boundary : c.2 % 27 = 0 ∧ c.1 % 18 < 9
  · refine ⟨(c.1 / 18,c.2 / 27 - 1),?_⟩
    rw [mem_microRegion]
    dsimp
    unfold MemberAt
    omega
  · refine ⟨(c.1 / 18,c.2 / 27),?_⟩
    rw [mem_microRegion]
    dsimp
    unfold MemberAt
    omega

/-- Distinct microcells can meet only at the two connector pixels between
vertically adjacent microcells. -/
theorem micro_overlap {i j c : Cell} (hi : c ∈ microRegion i) (hj : c ∈ microRegion j) :
    i = j ∨ (i.1 = j.1 ∧ (c.1 = 18 * i.1 + 5 ∨ c.1 = 18 * i.1 + 14) ∧
      ((i.2 + 1 = j.2 ∧ c.2 = 27 * j.2) ∨ (j.2 + 1 = i.2 ∧ c.2 = 27 * i.2))) := by
  rw [mem_microRegion] at hi hj
  simp only [Prod.ext_iff]
  unfold MemberAt at hi hj
  omega

end LeanTrominoes.CompletionPattern.IBricks
