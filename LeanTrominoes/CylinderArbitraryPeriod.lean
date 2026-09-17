/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CylinderPeriodicModel

/-! # Local periodic models for every nonzero period direction -/
namespace LeanTrominoes.Cylinder
set_option maxHeartbeats 1500000
variable {α : Type} [Fintype α]

def LocalModel (f g : Cell → α) (D : Finset Cell) (n : Nat) : Prop :=
  ∀ c, ∃ s : Cell, ∀ d ∈ D,
    g (Cell.add c d) = f (Cell.add (Cell.add c d) (Cell.scale (n+1:Int) s))

private theorem positive_model (f : Cell → α) (v : Cell) (hv : 0 < v.1)
    (periodic : IsPeriod f v) (D : Finset Cell) (n : Nat) :
    ∃ g u w, u.1*w.2-u.2*w.1 ≠ 0 ∧ IsPeriod g u ∧ IsPeriod g w ∧ LocalModel f g D n := by
  let a := v.1.toNat-1
  have eq : (a+1:Int) = v.1 := by dsimp [a]; omega
  have veq : v = ((a+1:Int),v.2) := by ext <;> simp [eq]
  rw [veq] at periodic
  obtain ⟨p,hp,g,hu,hw,copy⟩ := skew_model f a v.2 periodic D n
  refine ⟨g,((a+1:Int),v.2),((0:Int),(p:Int)),?_,hu,hw,?_⟩
  · dsimp
    simp only [mul_zero,sub_zero]
    exact mul_ne_zero (by omega) (by exact_mod_cast (ne_of_gt hp))
  · intro c
    obtain ⟨k,hk⟩ := copy c
    exact ⟨(0,k),by simpa [Cell.scale] using hk⟩

private theorem nonzero_x_model (f : Cell → α) (v : Cell) (hv : v.1 ≠ 0)
    (periodic : IsPeriod f v) (D : Finset Cell) (n : Nat) :
    ∃ g u w, u.1*w.2-u.2*w.1 ≠ 0 ∧ IsPeriod g u ∧ IsPeriod g w ∧ LocalModel f g D n := by
  by_cases pos : 0 < v.1
  · exact positive_model f v pos periodic D n
  · have negative : IsPeriod f (-v.1,-v.2) := by
      intro c; simpa [Cell.scale] using period_multiples periodic (-1) c
    exact positive_model f (-v.1,-v.2) (by dsimp; omega) negative D n

/-- Pumping preserves every requested local neighborhood and its square-lattice
phase, while adding a second independent period. -/
theorem local_model (f : Cell → α) (v : Cell) (hv : v ≠ (0,0))
    (periodic : IsPeriod f v) (D : Finset Cell) (n : Nat) :
    ∃ g u w, u.1*w.2-u.2*w.1 ≠ 0 ∧ IsPeriod g u ∧ IsPeriod g w ∧ LocalModel f g D n := by
  classical
  by_cases hx : v.1 ≠ 0
  · exact nonzero_x_model f v hx periodic D n
  · have hy : v.2 ≠ 0 := by intro h; apply hv; ext <;> simp_all
    let fs : Cell → α := fun c => f c.swap
    have hs : IsPeriod fs v.swap := by
      intro c; simpa [fs,Cell.add] using periodic c.swap
    obtain ⟨g,u,w,independent,hu,hw,copy⟩ :=
      nonzero_x_model fs v.swap hy hs (D.image Prod.swap) n
    refine ⟨fun c => g c.swap,u.swap,w.swap,?_,?_,?_,?_⟩
    · dsimp; intro eq; apply independent; nlinarith
    · intro c; simpa [Cell.add] using hu c.swap
    · intro c; simpa [Cell.add] using hw c.swap
    · intro c
      obtain ⟨s,hs⟩ := copy c.swap
      refine ⟨s.swap,?_⟩
      intro d hd
      have h := hs d.swap (Finset.mem_image.mpr ⟨d,hd,rfl⟩)
      simpa [fs,Cell.add,Cell.scale] using h
end LeanTrominoes.Cylinder
