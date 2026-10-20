/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATExpressions

/-! # Bounded arithmetic selection in flat table expressions

Integer division converts a bounded comparison to a zero/one value. Selection
then uses ordinary subtraction, multiplication, and addition. Every operation
is still checked by the expression compiler, including inactive alternatives.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATExpression
open ComplexityAbstract.RAM

def indicator (bound a b : ℤ) : ℤ := (b-a-1)/bound+1

theorem indicator_value (bound a b : ℤ) (_positive : 0<bound)
    (aNonnegative : 0≤a) (aSmall : a<bound) (bNonnegative : 0≤b) (bSmall : b<bound) :
    indicator bound a b=if a<b then 1 else 0 := by
  by_cases less : a<b
  · have quotient : (b-a-1)/bound=0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
    simp [indicator,quotient,less]
  · have quotient : (b-a-1)/bound= -1 := Int.ediv_eq_neg_one_of_neg_of_le (by omega) (by omega)
    simp [indicator,quotient,less]

def Expr.indicator {k : ℕ} (bound a b : Expr k) : Expr k :=
  .arithmetic .add (.arithmetic .div
    (.arithmetic .sub (.arithmetic .sub b a) (.constant 1)) bound) (.constant 1)

def Expr.selectLt {k : ℕ} (bound a b yes no : Expr k) : Expr k :=
  .arithmetic .add (.arithmetic .mul (Expr.indicator bound a b) yes)
    (.arithmetic .mul (.arithmetic .sub (.constant 1) (Expr.indicator bound a b)) no)

theorem Expr.indicator_eval {k : ℕ} (bound a b : Expr k) (env : Fin k → ℤ) (memory : ℕ → ℤ)
    (positive : 0<bound.eval env memory) (aNonnegative : 0≤a.eval env memory)
    (aSmall : a.eval env memory<bound.eval env memory) (bNonnegative : 0≤b.eval env memory)
    (bSmall : b.eval env memory<bound.eval env memory) :
    (Expr.indicator bound a b).eval env memory=if a.eval env memory<b.eval env memory then 1 else 0 := by
  exact indicator_value _ _ _ positive aNonnegative aSmall bNonnegative bSmall

theorem Expr.selectLt_eval {k : ℕ} (bound a b yes no : Expr k) (env : Fin k → ℤ) (memory : ℕ → ℤ)
    (positive : 0<bound.eval env memory) (aNonnegative : 0≤a.eval env memory)
    (aSmall : a.eval env memory<bound.eval env memory) (bNonnegative : 0≤b.eval env memory)
    (bSmall : b.eval env memory<bound.eval env memory) :
    (Expr.selectLt bound a b yes no).eval env memory=
      if a.eval env memory<b.eval env memory then yes.eval env memory else no.eval env memory := by
  simp only [selectLt,eval,Arithmetic.eval]
  change TwoSATExpression.indicator (bound.eval env memory) (a.eval env memory) (b.eval env memory)*yes.eval env memory+
    (1-TwoSATExpression.indicator (bound.eval env memory) (a.eval env memory) (b.eval env memory))*no.eval env memory=_
  rw [indicator_value _ _ _ positive aNonnegative aSmall bNonnegative bSmall]
  split <;> ring

theorem fits_interval {w : ℕ} {bound x : ℤ} (word : Fits w bound) (_positive : 0≤bound)
    (lower : -bound≤x) (upper : x≤bound) : Fits w x := by
  refine ⟨word.1,?_,upper.trans_lt word.2.2⟩
  have boundUpper := word.2.2
  omega

theorem Expr.safe_result {k w : ℕ} (e : Expr k) (env : Fin k → ℤ) (memory : ℕ → ℤ)
    (safe : e.Safe w env memory) : Fits w (e.eval env memory) := by
  cases e with
  | constant value => exact safe
  | inputValue index => exact safe
  | load address => exact safe.2.2.2
  | arithmetic op left right => exact safe.2.2

theorem Expr.indicator_safe {k w : ℕ} (bound a b : Expr k) (env : Fin k → ℤ) (memory : ℕ → ℤ)
    (boundSafe : bound.Safe w env memory) (aSafe : a.Safe w env memory) (bSafe : b.Safe w env memory)
    (positive : 0<bound.eval env memory) (aNonnegative : 0≤a.eval env memory)
    (aSmall : a.eval env memory<bound.eval env memory) (bNonnegative : 0≤b.eval env memory)
    (bSmall : b.eval env memory<bound.eval env memory) :
    (Expr.indicator bound a b).Safe w env memory := by
  have word := bound.safe_result env memory boundSafe
  have oneFits : Fits w 1 := fits_interval word (by omega) (by omega) (by omega)
  have difference : Fits w (b.eval env memory-a.eval env memory) :=
    fits_interval word (by omega) (by omega) (by omega)
  have adjusted : Fits w (b.eval env memory-a.eval env memory-1) :=
    fits_interval word (by omega) (by omega) (by omega)
  have quotientBounds : -1≤(b.eval env memory-a.eval env memory-1)/bound.eval env memory ∧
      (b.eval env memory-a.eval env memory-1)/bound.eval env memory≤0 := by
    by_cases less : a.eval env memory<b.eval env memory
    · rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
      omega
    · rw [Int.ediv_eq_neg_one_of_neg_of_le (by omega) (by omega)]
      omega
  have quotient : Fits w ((b.eval env memory-a.eval env memory-1)/bound.eval env memory) :=
    fits_interval word (by omega) (by omega) (by omega)
  have result : Fits w ((b.eval env memory-a.eval env memory-1)/bound.eval env memory+1) :=
    fits_interval word (by omega) (by omega) (by omega)
  exact ⟨⟨⟨⟨bSafe,aSafe,difference⟩,oneFits,adjusted⟩,boundSafe,quotient⟩,oneFits,result⟩

theorem Expr.selectLt_safe {k w : ℕ} (bound a b yes no : Expr k) (env : Fin k → ℤ) (memory : ℕ → ℤ)
    (boundSafe : bound.Safe w env memory) (aSafe : a.Safe w env memory) (bSafe : b.Safe w env memory)
    (yesSafe : yes.Safe w env memory) (noSafe : no.Safe w env memory)
    (positive : 0<bound.eval env memory) (aNonnegative : 0≤a.eval env memory)
    (aSmall : a.eval env memory<bound.eval env memory) (bNonnegative : 0≤b.eval env memory)
    (bSmall : b.eval env memory<bound.eval env memory) :
    (Expr.selectLt bound a b yes no).Safe w env memory := by
  let delta := Expr.indicator bound a b
  have deltaSafe : delta.Safe w env memory :=
    Expr.indicator_safe bound a b env memory boundSafe aSafe bSafe positive aNonnegative aSmall bNonnegative bSmall
  have deltaValue : delta.eval env memory=0 ∨ delta.eval env memory=1 := by
    dsimp only [delta]
    rw [Expr.indicator_eval bound a b env memory positive aNonnegative aSmall bNonnegative bSmall]
    split <;> simp
  have word := bound.safe_result env memory boundSafe
  have zeroFits : Fits w 0 := fits_interval word (by omega) (by omega) (by omega)
  have oneFits : Fits w 1 := fits_interval word (by omega) (by omega) (by omega)
  have yesFits := yes.safe_result env memory yesSafe
  have noFits := no.safe_result env memory noSafe
  have yesProduct : Fits w (delta.eval env memory*yes.eval env memory) := by
    rcases deltaValue with h | h
    · simpa only [h,zero_mul] using zeroFits
    · simpa only [h,one_mul] using yesFits
  have opposite : Fits w (1-delta.eval env memory) := by
    rcases deltaValue with h | h
    · simpa only [h,sub_zero] using oneFits
    · simpa only [h,sub_self] using zeroFits
  have noProduct : Fits w ((1-delta.eval env memory)*no.eval env memory) := by
    rcases deltaValue with h | h
    · simpa only [h,sub_zero,one_mul] using noFits
    · simpa only [h,sub_self,zero_mul] using zeroFits
  have result : Fits w (delta.eval env memory*yes.eval env memory+(1-delta.eval env memory)*no.eval env memory) := by
    rcases deltaValue with h | h
    · simpa only [h,zero_mul,sub_zero,one_mul,zero_add] using noFits
    · simpa only [h,one_mul,sub_self,zero_mul,add_zero] using yesFits
  exact ⟨⟨deltaSafe,yesSafe,yesProduct⟩,⟨⟨oneFits,deltaSafe,opposite⟩,noSafe,noProduct⟩,result⟩

end LeanTrominoes.ImplicationGraph.TwoSATExpression
