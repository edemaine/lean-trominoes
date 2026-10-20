/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATBudgets

/-! # A uniform polynomial word bound for fixed arithmetic/load expressions

Raw input integers need no magnitude bound. Two checked loads may instead be
certified by a bound on their difference. All other expression nodes satisfy
a conservative polynomial bound determined by the fixed expression size.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATExpression
open ComplexityAbstract.RAM

inductive Controlled {k : ℕ} (base : ℕ) (env : Fin k → ℤ) (memory : ℕ → ℤ) (input : List ℤ) : Expr k → Prop
  | constant (value : ℤ) : value.natAbs≤base → Controlled base env memory input (.constant value)
  | inputValue (i : Fin k) : (env i).natAbs≤base → Controlled base env memory input (.inputValue i)
  | arithmetic (op : Arithmetic) {a b : Expr k} : Controlled base env memory input a →
      Controlled base env memory input b → Controlled base env memory input (.arithmetic op a b)
  | load {address : Expr k} : Controlled base env memory input address → 0≤address.eval env memory →
      (memory (address.eval env memory).toNat).natAbs≤base → Controlled base env memory input (.load address)
  | difference {a b : Expr k} : Controlled base env memory input a → Controlled base env memory input b →
      0≤a.eval env memory → 0≤b.eval env memory →
      (∀ w, InputFits w input → Fits w (memory (a.eval env memory).toNat)) →
      (∀ w, InputFits w input → Fits w (memory (b.eval env memory).toNat)) →
      (memory (a.eval env memory).toNat-memory (b.eval env memory).toNat).natAbs≤base →
      Controlled base env memory input (.arithmetic .sub (.load a) (.load b))

variable {k base : ℕ} {env : Fin k → ℤ} {memory : ℕ → ℤ} {input : List ℤ}

theorem powBudget_mono (positive : 1≤base) (a b : ℕ) (le : a≤b) : base^a≤base^b :=
  Nat.pow_le_pow_right positive le

theorem arithmetic_power_budget (positive : 2≤base) (a b : ℕ) :
    (base^a+1)*(base^b+1)≤base^(a+b+2) := by
  have aPositive : 1≤base^a := Nat.one_le_pow _ _ (by omega)
  have bPositive : 1≤base^b := Nat.one_le_pow _ _ (by omega)
  have aBound : base^a+1≤base^(a+1) := by rw [pow_succ]; nlinarith
  have bBound : base^b+1≤base^(b+1) := by rw [pow_succ]; nlinarith
  have product := Nat.mul_le_mul aBound bBound
  simpa [← pow_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using product

theorem Controlled.budget {e : Expr k} (controlled : Controlled base env memory input e) (positive : 2≤base) :
    Bounded e (base^(2*e.nodes)) env memory input := by
  induction controlled with
  | constant value small =>
    apply (Bounded.constant value).mono
    exact small.trans (by simpa using powBudget_mono (base:=base) (by omega) 1 (2*(Expr.constant value : Expr k).nodes) (by simp only [Expr.nodes]; omega))
  | inputValue i small =>
    apply (Bounded.inputValue i base small).mono
    simpa only [Expr.nodes,Nat.mul_one,pow_one] using powBudget_mono (base:=base) (by omega) 1 2 (by omega)
  | @arithmetic op a b ha hb ia ib =>
    apply (Bounded.arithmetic op ia ib).mono
    simpa only [Expr.nodes,Nat.mul_add,Nat.mul_one] using arithmetic_power_budget positive (2*a.nodes) (2*b.nodes)
  | @load address controlled nonnegative small ih =>
    have addressBound : 2*address.nodes≤2*(Expr.load address).nodes := by simp only [Expr.nodes]; omega
    have resultBound : base≤base^(2*(Expr.load address).nodes) := by
      simpa using powBudget_mono (base:=base) (by omega) 1 (2*(Expr.load address).nodes) (by simp only [Expr.nodes]; omega)
    refine ⟨⟨?_⟩,small.trans resultBound⟩
    intro w word inputFits
    have addressWord : Fits w (base^(2*address.nodes)) :=
      fits_natAbs_le word (by simpa using powBudget_mono (base:=base) (by omega) _ _ addressBound)
    have safe := ih.safe w addressWord inputFits
    have addressFits := address.safe_result env memory safe
    have capacity : address.eval env memory<(2^w : ℕ) := by
      have h := Allocation.nat_address (show Fits w ((address.eval env memory).toNat : ℕ) by
        simpa only [Int.toNat_of_nonneg nonnegative] using addressFits)
      simpa only [Int.toNat_of_nonneg nonnegative] using h
    exact ⟨safe,nonnegative,capacity,fits_natAbs_le word (small.trans resultBound)⟩
  | @difference a b ca cb nonnegativeA nonnegativeB fitsA fitsB small ia ib =>
    let result : Expr k := .arithmetic .sub (.load a) (.load b)
    have aBound : 2*a.nodes≤2*result.nodes := by dsimp [result,Expr.nodes]; omega
    have bBound : 2*b.nodes≤2*result.nodes := by dsimp [result,Expr.nodes]; omega
    have resultBound : base≤base^(2*result.nodes) := by
      simpa using powBudget_mono (base:=base) (by omega) 1 (2*result.nodes) (by dsimp [result,Expr.nodes]; omega)
    refine ⟨⟨?_⟩,small.trans resultBound⟩
    intro w word inputFits
    have safeA := ia.safe w (fits_natAbs_le word (by simpa using powBudget_mono (base:=base) (by omega) _ _ aBound)) inputFits
    have safeB := ib.safe w (fits_natAbs_le word (by simpa using powBudget_mono (base:=base) (by omega) _ _ bBound)) inputFits
    have capacityA : a.eval env memory<(2^w : ℕ) := by
      have h := Allocation.nat_address (show Fits w ((a.eval env memory).toNat : ℕ) by
        simpa only [Int.toNat_of_nonneg nonnegativeA] using a.safe_result env memory safeA)
      simpa only [Int.toNat_of_nonneg nonnegativeA] using h
    have capacityB : b.eval env memory<(2^w : ℕ) := by
      have h := Allocation.nat_address (show Fits w ((b.eval env memory).toNat : ℕ) by
        simpa only [Int.toNat_of_nonneg nonnegativeB] using b.safe_result env memory safeB)
      simpa only [Int.toNat_of_nonneg nonnegativeB] using h
    exact ⟨⟨safeA,nonnegativeA,capacityA,fitsA w inputFits⟩,
      ⟨safeB,nonnegativeB,capacityB,fitsB w inputFits⟩,fits_natAbs_le word (small.trans resultBound)⟩

end LeanTrominoes.ImplicationGraph.TwoSATExpression
