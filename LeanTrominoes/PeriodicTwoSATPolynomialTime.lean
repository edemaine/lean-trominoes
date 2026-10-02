/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTwoSATSolver

/-! # Theorem 4.1: local periodic 2SAT is polynomial for every fixed dimension

The bound is conservative and includes period calculation, explicit base-M
indices, cover construction, query preparation, and the indexed Horn solver.
The model is the unit-cost indexed RAM, as in the other Section 4 solvers;
this is not a Lean VM timing or a formal bit-Turing runtime claim.
-/
namespace LeanTrominoes.PeriodicTwoSAT
open PeriodicLatticeGraph ImplicationGraph
variable {n d : Nat}

/-- Variable slots and at most two literals of fixed-dimensional local data per clause. -/
def inputSize (formula : Formula (Fin n) d) : Nat := n+formula.length+1

def coefficient (d : Nat) : Nat :=
  2000*(indexCharge d+10)*(d.factorial*11^d+(2*(d.factorial*11^d+1))^d+3)^3

def degree (d : Nat) : Nat := 3*(d*d+d+1)

theorem sizeBound_polynomial (formula : Formula (Fin n) d) :
    sizeBound formula ≤ (d.factorial*11^d+(2*(d.factorial*11^d+1))^d+3)*
      (inputSize formula)^(d*d+d+1) := by
  let s := inputSize formula
  let A := d.factorial*11^d
  let C := 2*(A+1)
  let D := determinantBound (2*n) d 2
  let k := d*d+d+1
  have positive : 1 ≤ s := by dsimp [s,inputSize]; omega
  have inner : (2*(2*n)+1)*2+1 ≤ 11*s := by dsimp [s,inputSize]; omega
  have determinant : D ≤ A*s^d := by
    have power := Nat.mul_le_mul_left d.factorial (Nat.pow_le_pow_left inner d)
    simpa [D,A,determinantBound,mul_pow,Nat.mul_assoc] using power
  have card : Fintype.card (Signed (Fin n))=2*n := by simp [Signed,Nat.mul_comm]
  have period_eq : period (Fin n) d=coverPeriod D := by simp [period,card,implicationPeriod,D]
  have period_bound : period (Fin n) d ≤ C*s^d := by
    have bound := coverPeriod_le D
    rw [← period_eq] at bound
    have powerPositive : 1 ≤ s^d := Nat.succ_le_of_lt (pow_pos (by omega) _)
    dsimp [C]
    nlinarith
  have cover_bound : (period (Fin n) d)^d ≤ C^d*s^(d*d) := by
    have power := Nat.pow_le_pow_left period_bound d
    simpa [mul_pow,← pow_mul] using power
  have low : d ≤ k := by dsimp [k]; omega
  have square : d*d ≤ k := by dsimp [k]; omega
  have one : 1 ≤ k := by dsimp [k]; omega
  have low_power := Nat.pow_le_pow_right positive low
  have square_power := Nat.pow_le_pow_right positive square
  have one_power : s ≤ s^k := by simpa using Nat.pow_le_pow_right positive one
  have determinant_high := determinant.trans (Nat.mul_le_mul_left A low_power)
  have cover_high := cover_bound.trans (Nat.mul_le_mul_left (C^d) square_power)
  have arcs_bound := arcs_length formula
  change sizeBound formula ≤ (A+C^d+3)*s^k
  unfold sizeBound
  have smallTerms : formula.length+n+(arcs formula).length+1 ≤ 3*s := by
    dsimp [s,inputSize]
    omega
  nlinarith

/-- The complete fixed-dimensional polynomial operation bound. -/
theorem polynomial_time (formula : Formula (Fin n) d) :
    (solve formula).2 ≤ coefficient d*(inputSize formula)^(degree d) := by
  have bounded := solve_cost_bound formula
  have power := Nat.pow_le_pow_left (sizeBound_polynomial formula) 3
  have scaled := Nat.mul_le_mul_left (2000*(indexCharge d+10)) power
  have combined := bounded.trans scaled
  simpa [coefficient,degree,mul_pow,← pow_mul,Nat.mul_assoc,Nat.mul_comm (d*d+d+1) 3] using combined

/-- Theorem 4.1, with an executable solver and a complete polynomial cost certificate. -/
theorem certified (formula : Formula (Fin n) d) (locality : Local formula) :
    ((solve formula).1=true ↔ Satisfiable formula) ∧
      (solve formula).2 ≤ coefficient d*(inputSize formula)^(degree d) :=
  ⟨solve_correct formula locality,polynomial_time formula⟩

end LeanTrominoes.PeriodicTwoSAT
