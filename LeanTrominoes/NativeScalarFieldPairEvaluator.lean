/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NativeScalarConjunction
import LeanTrominoes.PartrecDynamicDropSpace
import LeanTrominoes.PartrecBooleanUniformSpace

/-! # Combining a scalar verifier with a solver on the second native field block -/
noncomputable section
namespace LeanTrominoes.NativeScalar.FieldPair
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits Polynomial

def fields (first second : List Nat) : List Nat := first.length::(first++second)
def code (guard : Program) (body : Code) : Code := Code.boolAnd (normalize guard).code (body.comp Code.dynamicDropCode)
def result (guard : Program) (first second : List Nat) (answer : Bool) : Bool :=
  decide (guard.value (fields first second) ≠ 0) && answer

theorem code_eval (guard : Program) (body : Code) (first second : List Nat) (answer : Bool)
    (bodyEval : body.eval second=pure [answer.toNat]) :
    (code guard body).eval (fields first second)=pure [(result guard first second answer).toNat] := by
  have left := (normalize guard).evaluates (fields first second)
  rw [normalize_value] at left
  have right : (body.comp Code.dynamicDropCode).eval (fields first second)=pure [answer.toNat] := by
    simp [fields,Code.dynamicDropCode_eval,bodyEval,Part.bind_eq_bind]
  have both := Code.boolAnd_eval_at _ _ _ _ _ left right
  cases hg : decide (guard.value (fields first second) ≠ 0) <;> cases answer <;>
    simpa [code,result,hg] using both

def space (guard : Program) (bodySpace : Polynomial Nat) : Polynomial Nat :=
  1000*(X+C (normalize guard).coefficient*(X+1)+(bodySpace+1000000*(X+1))+2)

theorem code_fits (guard : Program) (body : Code) (first second : List Nat) (answer : Bool)
    (bodySpace : Polynomial Nat)
    (bodyFits : EvaluatorCodeFits body second [answer.toNat] (bodySpace.eval (encodedListSpace (fields first second)))) :
    EvaluatorCodeFits (code guard body) (fields first second) [(result guard first second answer).toNat]
      ((space guard bodySpace).eval (encodedListSpace (fields first second))) := by
  have left := (normalize guard).fits (fields first second)
  rw [normalize_value] at left
  have projection := dynamicDrop first.length (first++second)
  rw [List.drop_left] at projection
  have right := EvaluatorCodeFits.comp bodyFits projection
  have fit := boolAnd_bool left right
  simpa only [code,result,space,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one,dynamicDropCost,fields] using fit

theorem polynomial_mono (p : Polynomial Nat) {a b : Nat} (h : a≤b) : p.eval a≤p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n c => simp only [Polynomial.eval_monomial]; gcongr

end LeanTrominoes.NativeScalar.FieldPair

end
