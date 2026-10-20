/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATSelection
import LeanTrominoes.Computation.RAM.Allocation

/-! # Compositional budgets for checked integer expressions

Arbitrary input integers may be loaded when `InputFits` holds. They need not
have polynomial magnitude. A small difference of two such words receives its
own certificate. All subsequent fixed expressions have polynomial budgets.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATExpression
open ComplexityAbstract.RAM

theorem arithmeticBudget (a b : ℕ) : a+b≤(a+1)*(b+1) := by
  have eq : (a+1)*(b+1)=a*b+a+b+1 := by ring
  rw [eq]
  omega

theorem arithmetic_natAbs (op : Arithmetic) (x y : ℤ) :
    (op.eval x y).natAbs≤(x.natAbs+1)*(y.natAbs+1) := by
  cases op with
  | add => exact (Int.natAbs_add_le x y).trans (arithmeticBudget _ _)
  | sub => exact (Int.natAbs_sub_le x y).trans (arithmeticBudget _ _)
  | mul =>
    simp only [Arithmetic.eval,Int.natAbs_mul]
    exact Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
  | div =>
    exact (Int.natAbs_ediv_le_natAbs x y).trans ((Nat.le_add_right _ _).trans (arithmeticBudget _ _))
  | mod =>
    simp only [Arithmetic.eval]
    by_cases zero : y=0
    · subst y; simp
    · have low := Int.emod_nonneg x zero
      have high := Int.emod_lt_abs x zero
      have natHigh : (x%y).natAbs<y.natAbs := by
        rw [← Int.ofNat_lt,Int.natCast_natAbs,abs_of_nonneg low,Int.natCast_natAbs]
        exact high
      exact natHigh.le.trans ((Nat.le_add_left _ _).trans (arithmeticBudget _ _))

theorem fits_natAbs_le {w bound : ℕ} {value : ℤ} (word : Fits w bound) (small : value.natAbs≤bound) :
    Fits w value := by
  have le : (value.natAbs : ℤ)≤bound := Int.ofNat_le.mpr small
  rw [Int.natCast_natAbs] at le
  exact fits_interval word (Int.natCast_nonneg _) (abs_le.mp le).1 (abs_le.mp le).2

structure Checked {k : ℕ} (e : Expr k) (budget : ℕ) (env : Fin k → ℤ) (memory : ℕ → ℤ) (input : List ℤ) : Prop where
  safe : ∀ w, Fits w budget → InputFits w input → e.Safe w env memory

structure Bounded {k : ℕ} (e : Expr k) (budget : ℕ) (env : Fin k → ℤ) (memory : ℕ → ℤ) (input : List ℤ)
    : Prop extends Checked e budget env memory input where
  magnitude : (e.eval env memory).natAbs≤budget

variable {k : ℕ} {env : Fin k → ℤ} {memory : ℕ → ℤ} {input : List ℤ}

theorem Checked.mono {e : Expr k} {a b : ℕ} (checked : Checked e a env memory input) (le : a≤b) :
    Checked e b env memory input := by
  refine ⟨?_⟩
  intro w word inputFits
  exact checked.safe w (fits_natAbs_le word (by simpa using le)) inputFits

theorem Bounded.mono {e : Expr k} {a b : ℕ} (checked : Bounded e a env memory input) (le : a≤b) :
    Bounded e b env memory input := ⟨checked.toChecked.mono le,checked.magnitude.trans le⟩

theorem Bounded.constant (value : ℤ) : Bounded (.constant value : Expr k) value.natAbs env memory input := by
  refine ⟨⟨?_⟩,Nat.le_refl _⟩
  intro w word _
  exact fits_natAbs_le word (Nat.le_refl _)

theorem Bounded.inputValue (i : Fin k) (bound : ℕ) (small : (env i).natAbs≤bound) :
    Bounded (.inputValue i : Expr k) bound env memory input := by
  refine ⟨⟨?_⟩,small⟩
  intro w word _
  exact fits_natAbs_le word small

theorem Bounded.arithmetic (op : Arithmetic) {a b : Expr k} {aBudget bBudget : ℕ}
    (left : Bounded a aBudget env memory input) (right : Bounded b bBudget env memory input) :
    Bounded (.arithmetic op a b) ((aBudget+1)*(bBudget+1)) env memory input := by
  have aBound : aBudget≤(aBudget+1)*(bBudget+1) := by nlinarith
  have bBound : bBudget≤(aBudget+1)*(bBudget+1) := by nlinarith
  have leftMagnitude := left.magnitude
  have rightMagnitude := right.magnitude
  have magnitude : (op.eval (a.eval env memory) (b.eval env memory)).natAbs≤(aBudget+1)*(bBudget+1) :=
    (arithmetic_natAbs op _ _).trans (Nat.mul_le_mul (by omega : (a.eval env memory).natAbs+1≤aBudget+1)
      (by omega : (b.eval env memory).natAbs+1≤bBudget+1))
  refine ⟨⟨?_⟩,magnitude⟩
  intro w word inputFits
  exact ⟨left.safe w (fits_natAbs_le word (by simpa using aBound)) inputFits,
    right.safe w (fits_natAbs_le word (by simpa using bBound)) inputFits,fits_natAbs_le word magnitude⟩

theorem Checked.load {address : Expr k} {addressBudget : ℕ}
    (checked : Bounded address addressBudget env memory input) (nonnegative : 0≤address.eval env memory)
    (valueFits : ∀ w, InputFits w input → Fits w (memory (address.eval env memory).toNat)) :
    Checked (.load address) addressBudget env memory input := by
  refine ⟨?_⟩
  intro w word inputFits
  have safe := checked.safe w word inputFits
  have addressWord := address.safe_result env memory safe
  have addressFits : Fits w ((address.eval env memory).toNat : ℕ) := by
    simpa only [Int.toNat_of_nonneg nonnegative] using addressWord
  have capacity : address.eval env memory<(2^w : ℕ) := by
    have h := Allocation.nat_address addressFits
    simpa only [Int.toNat_of_nonneg nonnegative] using h
  exact ⟨safe,nonnegative,capacity,valueFits w inputFits⟩

theorem Bounded.load {address : Expr k} {addressBudget valueBudget : ℕ}
    (checked : Bounded address addressBudget env memory input) (nonnegative : 0≤address.eval env memory)
    (small : (memory (address.eval env memory).toNat).natAbs≤valueBudget) :
    Bounded (.load address) (addressBudget+valueBudget) env memory input := by
  have aBound : addressBudget≤addressBudget+valueBudget := by omega
  have vBound : valueBudget≤addressBudget+valueBudget := by omega
  refine ⟨⟨?_⟩,small.trans vBound⟩
  intro w word inputFits
  have safe := checked.safe w (fits_natAbs_le word (by simpa using aBound)) inputFits
  have addressWord := address.safe_result env memory safe
  have addressFits : Fits w ((address.eval env memory).toNat : ℕ) := by
    simpa only [Int.toNat_of_nonneg nonnegative] using addressWord
  have capacity : address.eval env memory<(2^w : ℕ) := by
    have h := Allocation.nat_address addressFits
    simpa only [Int.toNat_of_nonneg nonnegative] using h
  exact ⟨safe,nonnegative,capacity,fits_natAbs_le word (small.trans vBound)⟩

theorem Bounded.smallDifference {a b : Expr k} {aBudget bBudget magnitude : ℕ}
    (left : Checked a aBudget env memory input) (right : Checked b bBudget env memory input)
    (small : (a.eval env memory-b.eval env memory).natAbs≤magnitude) :
    Bounded (.arithmetic .sub a b) (aBudget+bBudget+magnitude) env memory input := by
  refine ⟨⟨?_⟩,small.trans (by omega)⟩
  intro w word inputFits
  exact ⟨left.safe w (fits_natAbs_le word (by simp; omega)) inputFits,
    right.safe w (fits_natAbs_le word (by simp; omega)) inputFits,
    fits_natAbs_le word (small.trans (by omega))⟩

end LeanTrominoes.ImplicationGraph.TwoSATExpression
