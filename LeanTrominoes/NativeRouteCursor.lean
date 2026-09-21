/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NativeScalarProgram

/-! # Native traversal of length-delimited point lists

At a route header the next route begins after one length field and twice the
stored point count. The cursor is a scalar; the input is never copied into a
nested natural-number encoding.
-/
namespace LeanTrominoes.NativeRouteCursor
open BoundedArithmetic BoundedArithmetic.Expr
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

def next (fields : List Nat) (cursor : Nat) : Nat := cursor+1+2*(fields[cursor]?.getD 0)
def advance (fields : List Nat) (count cursor : Nat) : Nat := (next fields)^[count] cursor

def step (v : List Nat) : List Nat := next v.tail v.headI :: v.tail

def expression : Expr := var 0+1+2*(.load (var 0+1))
def stepCode : Code := Code.prepend expression.code (Code.drop 1)

theorem stepCode_eval (v : List Nat) : stepCode.eval v = pure (step v) := by
  cases v <;> simp [stepCode,Code.prepend,Expr.code_eval,expression,Expr.eval,Op.eval,var,step,next,Part.bind_eq_bind]

theorem iterate_step (fields : List Nat) (count cursor : Nat) :
    (step^[count]) (cursor::fields) = advance fields count cursor :: fields := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [Function.iterate_succ_apply',ih]
    simp [advance,Function.iterate_succ_apply',step]

def code : Code := (Code.get 0).comp (Code.flatIterate stepCode)

theorem code_eval (fields : List Nat) (count cursor : Nat) :
    code.eval (count::cursor::fields) = pure [advance fields count cursor] := by
  simp [code,Code.flatIterate_eval _ _ stepCode_eval,iterate_step,Part.bind_eq_bind]

def stepCoefficient : Nat := 4*(expression.weight*(expression.radius+1)+20000+1)

theorem stepCode_fits (v : List Nat) :
    EvaluatorCodeFits stepCode v (step v) (stepCoefficient*(encodedListSpace v+1)) := by
  have fit := prepend_linear (expression.code_fits_automatic v (by decide)) (drop_linear 1 v)
  have value : expression.eval v = next v.tail v.headI := by
    cases v <;> simp [expression,Expr.eval,Op.eval,var,next]
  change EvaluatorCodeFits stepCode v (expression.eval v :: v.drop 1)
    (stepCoefficient*(encodedListSpace v+1)) at fit
  rw [value,List.drop_one] at fit
  exact fit

private theorem field_le_sum (fields : List Nat) (index : Nat) : fields[index]?.getD 0 ≤ fields.sum := by
  induction fields generalizing index with
  | nil => simp
  | cons a rest ih =>
    cases index with
    | zero => simp
    | succ index => simpa only [List.getElem?_cons_succ,List.sum_cons] using (ih index).trans (Nat.le_add_left _ _)

theorem advance_le (fields : List Nat) (count cursor : Nat) :
    advance fields count cursor ≤ cursor+count*(1+2*fields.sum) := by
  induction count with
  | zero => simp [advance]
  | succ count ih =>
    have h := field_le_sum fields (advance fields count cursor)
    rw [advance,Function.iterate_succ_apply']
    change next fields (advance fields count cursor) ≤ _
    unfold next
    nlinarith

private theorem sum_bits (fields : List Nat) :
    (Computability.encodeNat fields.sum).length ≤ encodedListSpace fields := by
  induction fields with
  | nil => rfl
  | cons a rest ih =>
    have h := encodeNat_add_length_le_sum a rest.sum
    simp only [List.sum_cons,encodedListSpace_cons]
    omega

theorem advance_bits (fields : List Nat) (count cursor : Nat) :
    (Computability.encodeNat (advance fields count cursor)).length ≤
      encodedListSpace (count::cursor::fields)+6 := by
  have bound := listCodeEncodeNat_length_mono (advance_le fields count cursor)
  have sum := sum_bits fields
  have mulTwo := encodeNat_mul_length_le_sum 2 fields.sum
  have addOne := encodeNat_add_length_le_sum 1 (2*fields.sum)
  have mulCount := encodeNat_mul_length_le_sum count (1+2*fields.sum)
  have total := encodeNat_add_length_le_sum cursor (count*(1+2*fields.sum))
  have one : (Computability.encodeNat 1).length=1 := rfl
  have two : (Computability.encodeNat 2).length=2 := rfl
  simp only [encodedListSpace_cons]
  omega

def iterationCoefficient : Nat := 100000*(10*stepCoefficient+2)

theorem iteration_fits (fields : List Nat) (count cursor : Nat) :
    EvaluatorCodeFits (Code.flatIterate stepCode) (count::cursor::fields)
      (advance fields count cursor :: fields)
      (iterationCoefficient*(encodedListSpace (count::cursor::fields)+1)) := by
  have countBits : (Computability.encodeNat count).length ≤ encodedListSpace (count::cursor::fields) := by
    simp only [encodedListSpace_cons]; omega
  have fit := flatIterate_uniform stepCode step (cursor::fields) count
    (10*stepCoefficient*(encodedListSpace (count::cursor::fields)+1))
    (encodedListSpace (count::cursor::fields)) countBits (by
      intro i hi
      rw [Function.iterate_succ_apply']
      apply (stepCode_fits _).mono
      have bits := advance_bits fields i cursor
      have small := listCodeEncodeNat_length_mono hi
      rw [iterate_step]
      simp only [encodedListSpace_cons] at bits ⊢
      nlinarith [Nat.mul_le_mul_left stepCoefficient bits])
  rw [iterate_step] at fit
  apply fit.mono
  unfold iterationBudget iterationCoefficient
  nlinarith

def coefficient : Nat := 100000+iterationCoefficient

theorem code_fits (fields : List Nat) (count cursor : Nat) :
    EvaluatorCodeFits code (count::cursor::fields) [advance fields count cursor]
      (coefficient*(encodedListSpace (count::cursor::fields)+1)) := by
  have bits := advance_bits fields count cursor
  have project := get_unit 0 (advance fields count cursor::fields)
    (10*(encodedListSpace (count::cursor::fields)+1)) (by
      simp only [encodedListSpace_cons] at bits ⊢
      omega)
  have fit := EvaluatorCodeFits.comp project (iteration_fits fields count cursor)
  simp only [List.getElem?_cons_zero,Option.getD_some] at fit
  apply fit.mono
  unfold coefficient
  nlinarith

end LeanTrominoes.NativeRouteCursor
