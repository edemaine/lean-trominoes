/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.Allocation
import LeanTrominoes.Common.Arithmetic.LatticePowerTwoSeparation

/-! # Computing the cover period by repeated bounded-word doubling

The logarithm in the mathematical specification is not a RAM instruction.
The program doubles from one until it exceeds the determinant bound.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATExpression
open ComplexityAbstract.RAM

variable {r w : ℕ}

def doublingProgram (current limit multiplier : Fin r) : Structured.Code r :=
  .loop (.lt current limit) (.atom (.arithmetic .mul current current multiplier))

theorem doubling_exec (current limit multiplier : Fin r) (data : Data r)
    (k threshold i : ℕ) (within : i≤k)
    (initial : data.1 current=2^i) (target : data.1 limit=threshold)
    (factor : data.1 multiplier=2) (differentLimit : limit≠current)
    (differentFactor : multiplier≠current)
    (lower : ∀ j, j<k → 2^j<threshold) (upper : threshold≤2^k)
    (word : Fits w (2^k : ℕ)) :
    Structured.Exec w (doublingProgram current limit multiplier) data
      (Function.update data.1 current (2^k : ℕ),data.2) (3*(k-i)+2) := by
  suffices ∀ remaining i, i+remaining=k → ∀ data : Data r,
      data.1 current=(2^i : ℕ) → data.1 limit=threshold → data.1 multiplier=2 →
      Structured.Exec w (doublingProgram current limit multiplier) data
        (Function.update data.1 current (2^k : ℕ),data.2) (3*remaining+2) by
    exact this (k-i) i (by omega) data initial target factor
  intro remaining
  induction remaining with
  | zero =>
    intro i endEq data initial target factor
    have same : i=k := by omega
    subst i
    have unchanged : Function.update data.1 current (2^k : ℕ)=data.1 := by
      rw [← initial]
      exact Function.update_eq_self _ _
    rw [unchanged]
    apply Structured.Exec.loop_done
    simp only [Structured.Condition.Holds,initial,target]
    exact not_lt.mpr (by exact_mod_cast upper)
  | succ remaining ih =>
    intro i endEq data initial target factor
    have nextWithin : i+1≤k := by omega
    have nextFits : Fits w (2^(i+1) : ℕ) :=
      Allocation.nat_fits_le word (Nat.pow_le_pow_right (by decide) nextWithin)
    let next : Data r := (Function.update data.1 current (2^(i+1) : ℕ),data.2)
    have step : Structured.Exec w (.atom (.arithmetic .mul current current multiplier)) data next 1 := by
      apply Structured.Exec.atom
      have value : ((2^i : ℕ) : ℤ)*2=(2^(i+1) : ℕ) := by simp [pow_succ]
      simp only [Structured.Primitive.eval,Arithmetic.eval,initial,factor,value,nextFits,ite_true,next]
    have nextCurrent : next.1 current=(2^(i+1) : ℕ) := by simp [next]
    have nextTarget : next.1 limit=threshold := by simp [next,Function.update_of_ne differentLimit,target]
    have nextFactor : next.1 multiplier=2 := by simp [next,Function.update_of_ne differentFactor,factor]
    have rest := ih (i+1) (by omega) next nextCurrent nextTarget nextFactor
    have run := Structured.Exec.loop_more (c:=Structured.Condition.lt current limit) (by
      simp only [Structured.Condition.Holds,initial,target]
      exact_mod_cast lower i (by omega)) step rest
    simp only [next,Function.update_idem] at run
    convert run using 1 <;> first | rfl | omega

theorem nextPower_lower (bound j : ℕ) (positive : 0<bound) (small : j<Nat.log2 bound+1) :
    2^j<bound+1 := by
  have power : 2^j≤bound := by
    exact (Nat.le_log2 (by omega : bound≠0)).mp (by omega)
  omega

theorem nextPower_upper (bound : ℕ) : bound+1≤2^(Nat.log2 bound+1) := by
  simpa only [coverPeriod,Nat.log2_eq_log_two] using Nat.succ_le_of_lt (coverPeriod_gt bound)

/-- Exact cost of computing the next strictly larger power of two from one. -/
theorem nextPower_exec (current limit multiplier : Fin r) (data : Data r) (bound : ℕ)
    (positive : 0<bound) (initial : data.1 current=1) (target : data.1 limit=bound+1)
    (factor : data.1 multiplier=2) (differentLimit : limit≠current)
    (differentFactor : multiplier≠current)
    (word : Fits w (2^(Nat.log2 bound+1) : ℕ)) :
    Structured.Exec w (doublingProgram current limit multiplier) data
      (Function.update data.1 current (2^(Nat.log2 bound+1) : ℕ),data.2)
      (3*(Nat.log2 bound+1)+2) := by
  simpa only [Nat.sub_zero] using doubling_exec current limit multiplier data (Nat.log2 bound+1)
    (bound+1) 0 (by omega) (by simpa using initial) target factor differentLimit differentFactor
      (fun j hj => nextPower_lower bound j positive hj) (nextPower_upper bound) word

end LeanTrominoes.ImplicationGraph.TwoSATExpression
