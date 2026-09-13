/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecBoundedArithmeticSpace

/-! # Automatic linear space bounds for the power-free arithmetic fragment -/

namespace LeanTrominoes.BoundedArithmetic
open Turing Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

theorem Expr.Safe.mono {expr : Expr} {values : List Nat} {small large : Nat}
    (h : small ≤ large) (safe : expr.Safe small values) : expr.Safe large values := by
  induction expr generalizing values with
  | literal n => exact safe.trans h
  | load i ih => exact ⟨ih safe.1,safe.2.trans h⟩
  | binary op a b ia ib => exact ⟨ia safe.1,ib safe.2.1,safe.2.2.trans h⟩
  | testBit a b ia ib => exact ⟨ia safe.1,ib safe.2.1,safe.2.2.trans h⟩
  | powerTwo a ih => exact ⟨ih safe.1,safe.2.trans h⟩
  | ite t y n it iy ino => exact ⟨it safe.1,iy safe.2.1,ino safe.2.2⟩
  | letE a b ia ib => exact ⟨ia safe.1,ib safe.2⟩
  | all n b ino ib => exact ⟨ino safe.1,safe.2.1.trans h,fun i hi => ib (safe.2.2 i hi)⟩

def Expr.noPower : Expr → Bool
  | .literal _ => true
  | .load i => i.noPower
  | .binary _ a b | .testBit a b => a.noPower && b.noPower
  | .powerTwo _ => false
  | .ite t y n => t.noPower && (y.noPower && n.noPower)
  | .letE a b | .all a b => a.noPower && b.noPower

/-- A constant bounding intermediate binary lengths in terms of the initial fields. -/
def Expr.radius : Expr → Nat
  | .literal n => (Computability.encodeNat n).length+1
  | .load i => i.radius+1
  | .binary _ a b | .testBit a b => a.radius+b.radius+1
  | .powerTwo _ => 1
  | .ite t y n => t.radius+y.radius+n.radius+1
  | .letE a b | .all a b => a.radius+b.radius*(a.radius+2)+1

theorem Expr.radius_pos (expr : Expr) : 0 < expr.radius := by
  cases expr <;> simp [Expr.radius] <;> omega

private theorem field_bits_le (values : List Nat) (index : Nat) :
    (Computability.encodeNat (values[index]?.getD 0)).length ≤ encodedListSpace values := by
  induction values generalizing index with
  | nil => simp only [List.getElem?_nil,Option.getD_none,encodedListSpace_nil]; change 0 ≤ 0; omega
  | cons a rest ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero,Option.getD_some,encodedListSpace_cons]; omega
    | succ index =>
      have h := ih index
      simpa only [List.getElem?_cons_succ] using h.trans (by simp [encodedListSpace_cons])

private theorem Op.eval_bits (op : Op) (a b : Nat) :
    (Computability.encodeNat (op.eval a b)).length ≤
      (Computability.encodeNat a).length+(Computability.encodeNat b).length+1 := by
  cases op with
  | add => exact encodeNat_add_length_le_sum a b
  | sub => exact (listCodeEncodeNat_length_mono (Nat.sub_le a b)).trans (by omega)
  | mul => exact (encodeNat_mul_length_le_sum a b).trans (by omega)
  | div => exact (listCodeEncodeNat_length_mono (Nat.div_le_self a b)).trans (by omega)
  | mod => exact (listCodeEncodeNat_length_mono (Nat.mod_le a b)).trans (by omega)
  | eq | lt =>
    simp only [Op.eval]
    split
    · change 1 ≤ _; omega
    · change 0 ≤ _; omega

set_option maxHeartbeats 800000 in
theorem Expr.safe_automatic (expr : Expr) (values : List Nat) (allowed : expr.noPower = true) :
    expr.Safe (expr.radius*(encodedListSpace values+1)) values := by
  induction expr generalizing values with
  | literal n =>
    change (Computability.encodeNat n).length ≤ ((Computability.encodeNat n).length+1)*(encodedListSpace values+1)
    nlinarith
  | load i ih =>
    have child := ih values allowed
    refine ⟨child.mono ?_,?_⟩
    · simp only [Expr.radius]; nlinarith
    · have h := field_bits_le values (i.eval values)
      simp only [Expr.eval,Expr.radius]
      nlinarith
  | binary op a b ia ib =>
    obtain ⟨hao,hbo⟩ := (by simpa only [Expr.noPower,Bool.and_eq_true] using allowed : a.noPower = true ∧ b.noPower = true)
    have sa := ia values hao
    have sb := ib values hbo
    refine ⟨sa.mono ?_,sb.mono ?_,?_⟩
    · simp only [Expr.radius]; nlinarith
    · simp only [Expr.radius]; nlinarith
    · have ha := sa.value_bits
      have hb := sb.value_bits
      have result := op.eval_bits (a.eval values) (b.eval values)
      simp only [Expr.radius]
      nlinarith
  | testBit a b ia ib =>
    obtain ⟨hao,hbo⟩ := (by simpa only [Expr.noPower,Bool.and_eq_true] using allowed : a.noPower = true ∧ b.noPower = true)
    refine ⟨(ia values hao).mono ?_,(ib values hbo).mono ?_,?_⟩
    · simp only [Expr.radius]; nlinarith
    · simp only [Expr.radius]; nlinarith
    · have h := (Expr.testBit a b).radius_pos
      have positive := Nat.mul_pos h (show 0 < encodedListSpace values+1 by omega)
      omega
  | powerTwo a ih => simp [Expr.noPower] at allowed
  | ite t y n it iy ino =>
    obtain ⟨ht,hy,hn⟩ := (by simpa only [Expr.noPower,Bool.and_eq_true] using allowed :
      t.noPower = true ∧ y.noPower = true ∧ n.noPower = true)
    refine ⟨(it values ht).mono ?_,(iy values hy).mono ?_,(ino values hn).mono ?_⟩ <;>
      simp only [Expr.radius] <;> nlinarith
  | letE a body ia ib =>
    obtain ⟨hao,hbo⟩ := (by simpa only [Expr.noPower,Bool.and_eq_true] using allowed : a.noPower = true ∧ body.noPower = true)
    have sa := ia values hao
    have ha := sa.value_bits
    have sb := ib (a.eval values :: values) hbo
    refine ⟨sa.mono ?_,sb.mono ?_⟩
    · simp only [Expr.radius]; nlinarith
    · have envBound : encodedListSpace (a.eval values :: values)+1 ≤
          (a.radius+2)*(encodedListSpace values+1) := by
        simp only [encodedListSpace_cons]
        nlinarith
      have bound := Nat.mul_le_mul_left body.radius envBound
      simp only [Expr.radius]
      nlinarith
  | all count body ic ib =>
    obtain ⟨hco,hbo⟩ := (by simpa only [Expr.noPower,Bool.and_eq_true] using allowed : count.noPower = true ∧ body.noPower = true)
    have sc := ic values hco
    have hc := sc.value_bits
    refine ⟨sc.mono ?_,?_,?_⟩
    · simp only [Expr.radius]; nlinarith
    · have h := (Expr.all count body).radius_pos
      have positive := Nat.mul_pos h (show 0 < encodedListSpace values+1 by omega)
      omega
    · intro i hi
      have hiBits := (listCodeEncodeNat_length_mono hi).trans hc
      have sb := ib (i :: values) hbo
      apply sb.mono
      have envBound : encodedListSpace (i :: values)+1 ≤
          (count.radius+2)*(encodedListSpace values+1) := by
        simp only [encodedListSpace_cons]
        nlinarith
      have bound := Nat.mul_le_mul_left body.radius envBound
      simp only [Expr.radius]
      nlinarith

/-- No per-input arithmetic safety certificate is needed for a power-free formula. -/
theorem Expr.code_fits_automatic (expr : Expr) (values : List Nat) (allowed : expr.noPower = true) :
    EvaluatorCodeFits expr.code values [expr.eval values]
      ((expr.weight*(expr.radius+1))*(encodedListSpace values+1)) := by
  have positive := Nat.mul_pos expr.radius_pos (show 0 < encodedListSpace values+1 by omega)
  have fitted := expr.code_fits values (expr.radius*(encodedListSpace values+1)) (by omega)
    (expr.safe_automatic values allowed)
  convert fitted using 1 <;> ring

end LeanTrominoes.BoundedArithmetic
