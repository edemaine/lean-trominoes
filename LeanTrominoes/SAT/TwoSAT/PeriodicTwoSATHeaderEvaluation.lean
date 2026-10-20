/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATHeaderExpressions

/-! # Evaluation of the complete arithmetic constructor header -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Header
open ImplicationGraph.TwoSATExpression Cells


private inductive Produces (memory : ℕ → ℤ) : List Statement → Env → Env → Prop where
  | nil (env : Env) : Produces memory [] env env
  | cons {a : Statement} {rest : List Statement} {env final : Env} {value : ℤ}
      (head : a.expression.eval env memory = value)
      (tail : Produces memory rest (Function.update env a.destination value) final) :
      Produces memory (a::rest) env final


private theorem Produces.sound {memory : ℕ → ℤ} {xs : List Statement} {env final : Env}
    (proof : Produces memory xs env final) : Assignment.evaluate xs env memory = final := by
  induction proof with
  | nil => rfl
  | cons head tail ih => simpa only [Assignment.evaluate,Assignment.update,head] using ih


set_option maxHeartbeats 2000000 in
theorem finish_values (d n m : ℕ) (env : Env) (memory : ℕ → ℤ)
    (vars : env 6=n) (clauseCount : env 7=m) (periodValue : env 8=period d n)
    (factor : env 0=2) :
    Assignment.evaluate (finish d) env memory=environment d n m := by
  let f0 := env
  let f1 : Env := Function.update f0 9 (coordinateCount d n : ℕ)
  have h1 : (power Cells.period d).eval f0 memory=(coordinateCount d n : ℕ) := by
    rw [power_eval]
    change (env 8)^d = ((period d n)^d : ℕ)
    rw [periodValue,Nat.cast_pow]
  let f2 : Env := Function.update f1 10 (vertexCount d n : ℕ)
  have h2 : (mul (two (increment numVars)) coordinates).eval f1 memory=(vertexCount d n : ℕ) := by
    simp [f1,f0,Cells.input,Cells.constant,Cells.increment,Cells.add,Cells.mul,Cells.two,Cells.three,
      Expr.eval,ComplexityAbstract.RAM.Arithmetic.eval,vars,clauseCount,periodValue,power_eval,vertexCount,
      Nat.cast_add,Nat.cast_mul,Nat.cast_pow] <;> ring_nf <;> simp
  let f3 : Env := Function.update f2 11 (edgeCount d n m : ℕ)
  have h3 : (mul coordinates (two clauses)).eval f2 memory=(edgeCount d n m : ℕ) := by
    simp [f2,f1,f0,Cells.input,Cells.constant,Cells.increment,Cells.add,Cells.mul,Cells.two,Cells.three,
      Expr.eval,ComplexityAbstract.RAM.Arithmetic.eval,vars,clauseCount,periodValue,power_eval,edgeCount,
      Nat.cast_add,Nat.cast_mul,Nat.cast_pow] <;> ring_nf <;> simp
  let f4 : Env := Function.update f3 12 (atomCount d n : ℕ)
  have h4 : (increment (mul (two numVars) vertices)).eval f3 memory=(atomCount d n : ℕ) := by
    simp [f3,f2,f1,f0,Cells.input,Cells.constant,Cells.increment,Cells.add,Cells.mul,Cells.two,Cells.three,
      Expr.eval,ComplexityAbstract.RAM.Arithmetic.eval,vars,clauseCount,periodValue,power_eval,atomCount,
      Nat.cast_add,Nat.cast_mul,Nat.cast_pow] <;> ring_nf <;> simp
  let f5 : Env := Function.update f4 13 (ruleCount d n m : ℕ)
  have h5 : (add (add (three numVars) (mul (two numVars) edges)) clauses).eval f4 memory=(ruleCount d n m : ℕ) := by
    simp [f4,f3,f2,f1,f0,Cells.input,Cells.constant,Cells.increment,Cells.add,Cells.mul,Cells.two,Cells.three,
      Expr.eval,ComplexityAbstract.RAM.Arithmetic.eval,vars,clauseCount,periodValue,power_eval,ruleCount,
      Nat.cast_add,Nat.cast_mul,Nat.cast_pow] <;> ring_nf <;> simp
  let f6 : Env := Function.update f5 14 (occurrenceCount d n m : ℕ)
  have h6 : (add (two numVars) (mul (two numVars) edges)).eval f5 memory=(occurrenceCount d n m : ℕ) := by
    simp [f5,f4,f3,f2,f1,f0,Cells.input,Cells.constant,Cells.increment,Cells.add,Cells.mul,Cells.two,Cells.three,
      Expr.eval,ComplexityAbstract.RAM.Arithmetic.eval,vars,clauseCount,periodValue,power_eval,occurrenceCount,
      Nat.cast_add,Nat.cast_mul,Nat.cast_pow] <;> ring_nf <;> simp
  let f7 : Env := Function.update f6 15 (size d n m : ℕ)
  have h7 : (increment (add (add atoms rules) occurrences)).eval f6 memory=(size d n m : ℕ) := by
    simp [f6,f5,f4,f3,f2,f1,f0,Cells.input,Cells.constant,Cells.increment,Cells.add,Cells.mul,Cells.two,Cells.three,
      Expr.eval,ComplexityAbstract.RAM.Arithmetic.eval,vars,clauseCount,periodValue,power_eval,size,
      Nat.cast_add,Nat.cast_mul,Nat.cast_pow] <;> ring_nf <;> simp
  let f8 : Env := Function.update f7 2 (length d n m : ℕ)
  have h8 : (add (add (constant 4) rules) (two occurrences)).eval f7 memory=(length d n m : ℕ) := by
    simp [f7,f6,f5,f4,f3,f2,f1,f0,Cells.input,Cells.constant,Cells.increment,Cells.add,Cells.mul,Cells.two,Cells.three,
      Expr.eval,ComplexityAbstract.RAM.Arithmetic.eval,vars,clauseCount,periodValue,power_eval,length,
      Nat.cast_add,Nat.cast_mul,Nat.cast_pow] <;> ring_nf <;> simp
  let f9 : Env := Function.update f8 16 (length d n m : ℕ)
  have h9 : (input 2).eval f8 memory=(length d n m : ℕ) := by
    simp [f8,f7,f6,f5,f4,f3,f2,f1,f0,Cells.input,Cells.constant,Cells.increment,Cells.add,Cells.mul,Cells.two,Cells.three,
      Expr.eval,ComplexityAbstract.RAM.Arithmetic.eval,vars,clauseCount,periodValue,power_eval,
      Nat.cast_add,Nat.cast_mul,Nat.cast_pow] <;> ring_nf <;> simp
  let f10 : Env := Function.update f9 5 (arena d n m : ℕ)
  have detValue : (determinant d).eval f9 memory=(bound d n : ℕ) := by
    apply determinant_eval
    simp [f9,f8,f7,f6,f5,f4,f3,f2,f1,f0,vars]
  have baseValue : (add (add (add (add (add (input 15) (determinant d)) coordinates) numVars) (three Cells.clauses)) (constant 4)).eval f9 memory=
      (size d n m+bound d n+coordinateCount d n+n+3*m+4 : ℕ) := by
    simp [f9,f8,f7,f6,f5,f4,f3,f2,f1,f0,Cells.input,Cells.constant,Cells.add,Cells.three,Cells.mul,
      Expr.eval,ComplexityAbstract.RAM.Arithmetic.eval,vars,clauseCount,detValue,
      Nat.cast_add,Nat.cast_mul]
  have h10 : (mul (constant (4*(Raw.recordSize d+1))) (power (add (add (add (add (add (input 15) (determinant d)) coordinates) numVars) (three Cells.clauses)) (constant 4)) 27)).eval f9 memory=(arena d n m : ℕ) := by
    change ((4*(Raw.recordSize d+1) : ℕ) : ℤ)*(power (add (add (add (add (add (input 15) (determinant d)) coordinates) numVars) (three Cells.clauses)) (constant 4)) 27).eval f9 memory=_
    rw [power_eval,baseValue]
    simp only [arena,Nat.cast_mul,Nat.cast_pow]
  let f11 : Env := Function.update f10 1 (0 : ℕ)
  have h11 : (constant 0).eval f10 memory=(0 : ℕ) := by
    rfl
  let f12 : Env := Function.update f11 3 (0 : ℕ)
  have h12 : (constant 0).eval f11 memory=(0 : ℕ) := by
    rfl
  let f13 : Env := Function.update f12 4 (1 : ℕ)
  have h13 : (constant 1).eval f12 memory=(1 : ℕ) := by
    rfl
  have execution : Produces memory (finish d) f0 f13 :=
    .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7
      (.cons h8 (.cons h9 (.cons h10 (.cons h11 (.cons h12 (.cons h13 (.nil f13)))))))))))))
  have finalEqual : f13=environment d n m := by
    funext i
    fin_cases i <;> dsimp [f13,f12,f11,f10,f9,f8,f7,f6,f5,f4,f3,f2,f1,f0,environment,Function.update]
    all_goals first | rfl | assumption
  exact (Produces.sound execution).trans finalEqual

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Header
