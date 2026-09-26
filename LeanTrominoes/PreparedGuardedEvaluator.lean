/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PreparedFieldPairCompiler
import LeanTrominoes.BoundedArithmeticSlice
import LeanTrominoes.PartrecDynamicDropSpace
import LeanTrominoes.PartrecBooleanUniformSpace
import LeanTrominoes.PartrecPreparedEvaluatorSpace

/-! # Combining a native validity guard with a prepared space-bounded evaluator -/
noncomputable section
namespace LeanTrominoes.PreparedGuardedEvaluator
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open BoundedArithmetic Polynomial
set_option maxRecDepth 100000

variable {Input : Type} (encoding : _root_.Computability.FinEncoding Input)
  [Inhabited encoding.Γ]
  (first second : Input → List Nat)
  (cf : TM2ComputableInPolyTime encoding.encode trList first)
  (cs : TM2ComputableInPolyTime encoding.encode trList second)

def fields (x : Input) : List Nat := (first x).length :: (first x ++ second x)

def preparation : TM2ComputableInPolyTime encoding.encode trList (fields first second) :=
  preparedFieldPairCompiler cf cs

def inputPolynomial : Polynomial Nat :=
  TM2OutputLength.outputLengthPolynomial (preparation encoding first second cf cs)

theorem fields_space (x : Input) : encodedListSpace (fields first second x) ≤
    (inputPolynomial encoding first second cf cs).eval (encoding.encode x).length := by
  have bound := TM2OutputLength.output_length_le_polynomial_eval
    (preparation encoding first second cf cs) x
  exact bound

variable (guard : Expr) (guardResult : Input → Bool)
  (guardEval : ∀ x, guard.eval (first x) = (guardResult x).toNat)
  (allowed : guard.noPower = true)
  (body : Code) (bodyResult : Input → Bool)
  (bodyEval : ∀ x, body.eval (second x) = pure [(bodyResult x).toNat])
  (bodySpace : Polynomial Nat)
  (bodyFits : ∀ x, EvaluatorCodeFits body (second x) [(bodyResult x).toNat]
    (bodySpace.eval (encoding.encode x).length))

def sliced : Expr := guard.slice 0

def code : Code := Code.boolAnd (sliced guard).code (body.comp Code.dynamicDropCode)
def result (x : Input) : Bool := guardResult x && bodyResult x

include guardEval in
theorem sliced_eval (x : Input) : (sliced guard).eval (fields first second x) = (guardResult x).toNat := by
  have h := Expr.slice_eval guard [] (first x) (second x)
  simpa only [sliced,fields,List.length_nil,List.nil_append,guardEval] using h

include guardEval bodyEval in
theorem code_eval (x : Input) :
    (code guard body).eval (fields first second x) = pure [(result guardResult bodyResult x).toNat] := by
  have left : (sliced guard).code.eval (fields first second x) = pure [(guardResult x).toNat] := by
    rw [Expr.code_eval,sliced_eval first second guard guardResult guardEval]
  have right : (body.comp Code.dynamicDropCode).eval (fields first second x) = pure [(bodyResult x).toNat] := by
    simp [fields,Code.dynamicDropCode_eval,bodyEval,Part.bind_eq_bind]
  have h := Code.boolAnd_eval_at (sliced guard).code (body.comp Code.dynamicDropCode)
    (fields first second x) (guardResult x).toNat (bodyResult x).toNat left right
  cases ha : guardResult x <;> cases hb : bodyResult x <;>
    simpa [code,result,ha,hb] using h

def coefficient : Nat := (sliced guard).weight*((sliced guard).radius+1)

def space : Polynomial Nat :=
  let p := inputPolynomial encoding first second cf cs
  1000*(p+C (coefficient guard)*(p+1)+(bodySpace+C 1000000*(p+1))+2)

include guardEval allowed bodyFits in
theorem code_fits (x : Input) :
    EvaluatorCodeFits (code guard body) (fields first second x) [(result guardResult bodyResult x).toNat]
      ((space encoding first second cf cs guard bodySpace).eval (encoding.encode x).length) := by
  have bound := fields_space encoding first second cf cs x
  have left := (sliced guard).code_fits_automatic (fields first second x)
    (by simpa only [sliced,Expr.slice_noPower] using allowed)
  rw [sliced_eval first second guard guardResult guardEval] at left
  have projection := dynamicDrop (first x).length (first x ++ second x)
  rw [List.drop_left] at projection
  have right := EvaluatorCodeFits.comp (bodyFits x) projection
  have fit := boolAnd_bool left right
  apply fit.mono
  simp only [space,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_ofNat,Polynomial.eval_one,dynamicDropCost,coefficient,fields] at *
  gcongr

def decider (language : Input → Prop)
    (correct : ∀ x, result guardResult bodyResult x = true ↔ language x) :
    Complexity.DeciderInPolySpace encoding language :=
  deciderInPolySpace_of_preparedEvaluator encoding (fields first second)
    (Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
      (preparation encoding first second cf cs))
    (code guard body) language (result guardResult bodyResult) correct
    (fun x => by
      rw [code_eval first second guard guardResult guardEval body bodyResult bodyEval]
      apply Part.mem_some_iff.mpr
      cases result guardResult bodyResult x <;> rfl)
    (space encoding first second cf cs guard bodySpace)
    (fun x => by
      let fit := code_fits encoding first second cf cs guard guardResult guardEval allowed
        body bodyResult bodySpace bodyFits x
      let after := EvaluatorExecutionFits.ret_halt fit.output_space
      apply EvaluatorRunFits.of_call
      exact fit.call .halt _ (by simp [continuationSpace,trContStack]) after)

end LeanTrominoes.PreparedGuardedEvaluator
end
