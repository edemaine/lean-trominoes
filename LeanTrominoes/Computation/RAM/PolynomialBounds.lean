/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.WordBounds
import Mathlib.Tactic

/-! # Compositional polynomial bounds for two finite input counts -/
namespace LeanTrominoes.WordBounds

/-- Constants and exponents are uniform over both input counts. -/
def PolynomialBound (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ C k, ∀ n m, f n m≤C*(n+m+2)^k

namespace PolynomialBound
variable {f g : ℕ → ℕ → ℕ}

theorem constant (a : ℕ) : PolynomialBound (fun _ _ => a) :=
  ⟨a,0,by intro n m; simp⟩

theorem left : PolynomialBound (fun n _ => n) := by
  refine ⟨1,1,?_⟩
  intro n m
  simp only [pow_one,Nat.one_mul]
  omega

theorem right : PolynomialBound (fun _ m => m) := by
  refine ⟨1,1,?_⟩
  intro n m
  simp only [pow_one,Nat.one_mul]
  omega

theorem mono (h : PolynomialBound g) (le : ∀ n m, f n m≤g n m) : PolynomialBound f := by
  obtain ⟨C,k,bound⟩ := h
  exact ⟨C,k,fun n m => (le n m).trans (bound n m)⟩

theorem add (a : PolynomialBound f) (b : PolynomialBound g) :
    PolynomialBound (fun n m => f n m+g n m) := by
  obtain ⟨C,k,first⟩ := a
  obtain ⟨D,l,second⟩ := b
  refine ⟨C+D,k+l,?_⟩
  intro n m
  have positive : 1≤n+m+2 := by omega
  have p := Nat.pow_le_pow_right positive (show k≤k+l by omega)
  have q := Nat.pow_le_pow_right positive (show l≤k+l by omega)
  have x := (first n m).trans (Nat.mul_le_mul_left C p)
  have y := (second n m).trans (Nat.mul_le_mul_left D q)
  nlinarith

theorem mul (a : PolynomialBound f) (b : PolynomialBound g) :
    PolynomialBound (fun n m => f n m*g n m) := by
  obtain ⟨C,k,first⟩ := a
  obtain ⟨D,l,second⟩ := b
  refine ⟨C*D,k+l,?_⟩
  intro n m
  have h := Nat.mul_le_mul (first n m) (second n m)
  simpa only [pow_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

theorem pow (a : PolynomialBound f) (p : ℕ) : PolynomialBound (fun n m => f n m^p) := by
  obtain ⟨C,k,bound⟩ := a
  refine ⟨C^p,k*p,?_⟩
  intro n m
  simpa only [mul_pow,← pow_mul] using Nat.pow_le_pow_left (bound n m) p

/-- A shared logarithmic width suffices for every value bounded this way. -/
theorem fits (h : PolynomialBound f) :
    ∃ k, ∀ n m w, k*Nat.log2 (n+m+3)+2≤w →
      ComplexityAbstract.RAM.Fits w (f n m : ℕ) := by
  obtain ⟨C,e,bound⟩ := h
  refine ⟨Nat.log2 (C+1)+2*e,?_⟩
  intro n m w width
  apply polynomial_fits_uniform C e (n+m+1) w (f n m) (by simpa [Nat.add_assoc] using width)
  simpa only [Int.natAbs_natCast,Nat.add_assoc] using bound n m

end PolynomialBound
end LeanTrominoes.WordBounds
