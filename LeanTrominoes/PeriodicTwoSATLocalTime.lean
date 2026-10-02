/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTwoSATPolynomialTime
import LeanTrominoes.PeriodicTwoSATNormalization

/-! # Theorem 4.1 under locality of offset differences

This endpoint includes clause normalization, so input clauses may have large
common offsets. Coordinatewise difference locality is more general than the
paper's Manhattan-distance-one locality. Variables are explicit dense slots;
costs count indexed-RAM operations, including normalization and preparation.
-/
namespace LeanTrominoes.PeriodicTwoSAT
variable {n d : Nat}

def solveLocal (formula : Formula (Fin n) d) : Bool × Nat :=
  let anchored := normalize formula
  let result := solve anchored
  (result.1,result.2+formula.length*(3*d+5)+1)

theorem solveLocal_correct (formula : Formula (Fin n) d) (locality : LocalDifferences formula) :
    (solveLocal formula).1=true ↔ Satisfiable formula :=
  (solve_correct (normalize formula) (normalize_local formula locality)).trans (normalize_satisfiable formula)

def localCoefficient (d : Nat) : Nat := coefficient d+3*d+6

theorem solveLocal_polynomial (formula : Formula (Fin n) d) :
    (solveLocal formula).2 ≤ localCoefficient d*(inputSize formula)^(degree d) := by
  have solverBound := polynomial_time (normalize formula)
  have size : inputSize (normalize formula)=inputSize formula := by simp [inputSize]
  rw [size] at solverBound
  have positive : 1 ≤ inputSize formula := by unfold inputSize; omega
  have exponent : 1 ≤ degree d := by unfold degree; omega
  have power : inputSize formula ≤ (inputSize formula)^(degree d) := by
    simpa using Nat.pow_le_pow_right positive exponent
  have lengthBound : formula.length ≤ inputSize formula := by unfold inputSize; omega
  have normalization := Nat.mul_le_mul_right (3*d+5) (lengthBound.trans power)
  have one : 1 ≤ (inputSize formula)^(degree d) := positive.trans power
  unfold solveLocal localCoefficient
  nlinarith

/-- Theorem 4.1: an executable decision and polynomial operation bound in every fixed d. -/
theorem local_certified (formula : Formula (Fin n) d) (locality : LocalDifferences formula) :
    ((solveLocal formula).1=true ↔ Satisfiable formula) ∧
      (solveLocal formula).2 ≤ localCoefficient d*(inputSize formula)^(degree d) :=
  ⟨solveLocal_correct formula locality,solveLocal_polynomial formula⟩

end LeanTrominoes.PeriodicTwoSAT
