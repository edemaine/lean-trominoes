/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripCompilerData

/-! # Native evaluator program that emits the uncovered strip fields -/
namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Compiler
open BoundedArithmetic BoundedArithmetic.Expr
open Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

/-- Payload header: packed output, output field count, grid index. -/
def testExpr (t : Tromino) : Expr :=
  .letE (var 2 / var 4) (.letE (var 3 % var 5) (coveredExpr t 5 1 0))

def baseExpr : Expr := 2*(var 4+var 5+1)
def appendedExpr : Expr := 2*(var 2 % var 4)+baseExpr*(2*(var 2/var 4)+baseExpr*var 0)
def wordExpr (t : Tromino) : Expr := .ite (testExpr t) (var 0) appendedExpr
def countExpr (t : Tromino) : Expr := .ite (testExpr t) (var 1) (var 1+2)

def step (t : Tromino) (values : List Nat) : List Nat :=
  let occupied := (testExpr t).eval values ≠ 0
  let word := values[0]?.getD 0
  let count := values[1]?.getD 0
  let index := values[2]?.getD 0
  let height := values[4]?.getD 0
  let radix := 2*(height+values[5]?.getD 0+1)
  [if occupied then word else 2*(index%height)+radix*(2*(index/height)+radix*word),
    if occupied then count else count+2,index+1] ++ values.drop 3

def stepCode (t : Tromino) : Code := Code.prepend (wordExpr t).code
  (Code.prepend (countExpr t).code (Code.prepend (var 2+1).code (Code.drop 3)))

theorem step_eval (t : Tromino) (values : List Nat) : (stepCode t).eval values = pure (step t values) := by
  simp only [stepCode,Code.prepend_eval_eq,Expr.code_eval,Code.drop_eval,Part.bind_eq_bind,Part.bind_some]
  by_cases h : (testExpr t).eval values = 0
  · simp [step,wordExpr,countExpr,Expr.eval,h,appendedExpr,baseExpr,Op.eval,var]
  · simp [step,wordExpr,countExpr,Expr.eval,h,appendedExpr,baseExpr,Op.eval,var]

theorem test_truth (t : Tromino) (input : PeriodicStripTrominoPrefill) (word count index : Nat) :
    (testExpr t).Truth ([word,count,index]++fields input) ↔
      Covered t input (index/input.height) (index%input.height) := by
  have h := coveredExpr_truth t input [index%input.height,index/input.height,word,count,index]
    1 0 (index/input.height) (index%input.height) rfl rfl
  exact h

theorem step_payload (t : Tromino) (input : PeriodicStripTrominoPrefill) (index : Nat) :
    step t (payload t input index) = payload t input (index+1) := by
  have test := test_truth t input (PackedFields.pack (base input) (records t input index).reverse)
    (records t input index).length index
  change ((testExpr t).eval (payload t input index) ≠ 0) ↔ _ at test
  unfold payload at test ⊢
  rw [records_succ]
  by_cases h : Covered t input (index/input.height) (index%input.height)
  · have occupied := test.mpr h
    simp only [fields,CompletionStripEncoding.fields,List.cons_append,List.nil_append] at occupied
    simp [step,h,occupied,fields,CompletionStripEncoding.fields]
  · have absent : ¬ (testExpr t).eval ([PackedFields.pack (base input) (records t input index).reverse,
        (records t input index).length,index]++fields input) ≠ 0 := fun hp => h (test.mp hp)
    simp only [fields,CompletionStripEncoding.fields,List.cons_append,List.nil_append,base] at absent
    simp [step,h,absent,fields,CompletionStripEncoding.fields,List.reverse_append,PackedFields.pack,base]

theorem iterate_payload (t : Tromino) (input : PeriodicStripTrominoPrefill) (n : Nat) :
    ((step t)^[n]) ([0,0,0]++fields input) = payload t input n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,step_payload]

def initializeCode : Code := Code.prepend (var 1*var 2).code
  (Code.prepend Code.zero (Code.prepend Code.zero (Code.prepend Code.zero Code.id)))

def finishCode : Code :=
  Code.prepend (Code.get 4) (Code.prepend (Code.get 5) (Code.prepend (var 1/2).code
    (PackedFields.unpackCode.comp (Code.prepend (Code.get 1) (Code.prepend (Code.get 0) baseExpr.code)))))

def compileCode (t : Tromino) : Code := finishCode.comp ((Code.flatIterate (stepCode t)).comp initializeCode)


theorem initialize_eval (input : PeriodicStripTrominoPrefill) :
    initializeCode.eval (fields input) =
      pure ((input.period*input.height)::([0,0,0]++fields input)) := by
  simp [initializeCode,Code.prepend_eval_eq,Expr.code_eval,fields,
    CompletionStripEncoding.fields,Part.bind_eq_bind,Nat.mul_comm]

theorem finish_eval (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (hh : 0 < input.height) (n : Nat) (hn : n ≤ input.period*input.height) :
    finishCode.eval (payload t input n) =
      pure ([input.height,input.period,(emitted t input n).length]++records t input n) := by
  have bounded : ∀ a ∈ (records t input n).reverse, a < base input := by
    simpa using records_bounded t input hh n hn
  have unpack := PackedFields.unpack_eval (base input) (records t input n).reverse bounded
  simp only [List.reverse_reverse,List.length_reverse] at unpack
  have extract :
      (Code.prepend (Code.get 1) (Code.prepend (Code.get 0) baseExpr.code)).eval
        (payload t input n) = pure [(records t input n).length,
          PackedFields.pack (base input) (records t input n).reverse,base input] := by
    simp [Code.prepend_eval_eq,Expr.code_eval,payload,fields,CompletionStripEncoding.fields,
      baseExpr,base,Part.bind_eq_bind,Expr.eval,Op.eval]
  have core : (PackedFields.unpackCode.comp
      (Code.prepend (Code.get 1) (Code.prepend (Code.get 0) baseExpr.code))).eval
      (payload t input n) = pure (records t input n) := by
    change ((Code.prepend (Code.get 1) (Code.prepend (Code.get 0) baseExpr.code)).eval
      (payload t input n)).bind PackedFields.unpackCode.eval = _
    rw [extract]
    simpa only [Part.pure_eq_some,Part.bind_some] using unpack
  simp only [finishCode,Code.prepend_eval_eq,Code.get_eval,Expr.code_eval,core,
    Part.bind_eq_bind,Part.bind_some]
  simp [payload,fields,CompletionStripEncoding.fields,records_length,Expr.eval,Op.eval]

theorem compile_eval (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (hh : 0 < input.height) :
    (compileCode t).eval (fields input) =
      pure (PeriodicStripFlatEncoding.stripFields (compiledStrip t input)) := by
  have loop := Code.flatIterate_eval (stepCode t) (step t) (step_eval t)
    (input.period*input.height) ([0,0,0]++fields input)
  rw [iterate_payload] at loop
  change (((initializeCode.eval (fields input)).bind (Code.flatIterate (stepCode t)).eval).bind
    finishCode.eval) = _
  rw [initialize_eval]
  simp only [Part.pure_eq_some,Part.bind_some]
  rw [loop]
  simpa only [Part.pure_eq_some,Part.bind_some,PeriodicStripFlatEncoding.stripFields,compiledStrip,records] using finish_eval t input hh _ le_rfl

theorem test_noPower (t : Tromino) : (testExpr t).noPower = true := by
  simp [testExpr,Expr.noPower,coveredExpr_noPower]

theorem word_noPower (t : Tromino) : (wordExpr t).noPower = true := by
  simp [wordExpr,appendedExpr,baseExpr,Expr.noPower,test_noPower]

theorem count_noPower (t : Tromino) : (countExpr t).noPower = true := by
  simp [countExpr,Expr.noPower,test_noPower]

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Compiler
