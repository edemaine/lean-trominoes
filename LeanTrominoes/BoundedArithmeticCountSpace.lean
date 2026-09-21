/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BoundedArithmeticCount

/-! # Linear evaluator space for counting bounded witnesses -/
namespace LeanTrominoes.BoundedArithmetic.Count
open Expr Turing Turing.ToPartrec Turing.PartrecToTM2
open Turing.PartrecToTM2.EvaluatorCodeFits

theorem state_space (body : Expr) (values : List Nat) (n i : Nat) (hi : i ≤ n) :
    encodedListSpace (((step body)^[i]) (0::0::values)) ≤ 2*encodedListSpace (n::values)+2 := by
  rw [iterate_step]
  have a := listCodeEncodeNat_length_mono ((count_le body values i).trans hi)
  have b := listCodeEncodeNat_length_mono hi
  simp only [encodedListSpace_cons]
  omega

def iterationCoefficient (body : Expr) : Nat := 100000*(3*stepCoefficient body+2)

theorem iteration_fits (body : Expr) (allowed : body.noPower = true) (values : List Nat) (n : Nat) :
    EvaluatorCodeFits (Code.flatIterate (stepCode body)) (n::0::0::values)
      (count body values n :: n :: values)
      (iterationCoefficient body*(encodedListSpace (n::values)+1)) := by
  have run := flatIterate_uniform (stepCode body) (step body) (0::0::values) n
    (3*stepCoefficient body*(encodedListSpace (n::values)+1))
    (encodedListSpace (n::values)) (by simp only [encodedListSpace_cons]; omega) (by
      intro i hi
      rw [Function.iterate_succ_apply']
      apply (stepCode_fits body allowed _).mono
      have h := state_space body values n i hi
      nlinarith [Nat.mul_le_mul_left (stepCoefficient body) h])
  rw [iterate_step] at run
  apply run.mono
  simp only [iterationBudget,iterationCoefficient]
  nlinarith

def inputCoefficient : Nat := 4*(10000+4*(10000+4*(10000+20000+1)+1)+1)

theorem inputCode_fits (values : List Nat) (n : Nat) :
    EvaluatorCodeFits inputCode (n::values) (n::0::0::values)
      (inputCoefficient*(encodedListSpace (n::values)+1)) := by
  have z := zero_unit (n::values) (encodedListSpace (n::values)+1) le_rfl
  have fit := prepend_linear (get_linear 0 (n::values))
    (prepend_linear z (prepend_linear z (drop_linear 1 (n::values))))
  simpa only [inputCode,inputCoefficient,List.getElem?_cons_zero,Option.getD_some,
    List.drop_succ_cons,List.drop_zero] using fit

def coefficient (body : Expr) : Nat := 20000+iterationCoefficient body+inputCoefficient

theorem code_fits (body : Expr) (allowed : body.noPower = true) (values : List Nat) (n : Nat) :
    EvaluatorCodeFits (code body) (n::values) [count body values n]
      (coefficient body*(encodedListSpace (n::values)+1)) := by
  have run := EvaluatorCodeFits.comp (iteration_fits body allowed values n) (inputCode_fits values n)
  have size : encodedListSpace (count body values n :: n :: values)+1 ≤
      2*(encodedListSpace (n::values)+1) := by
    have h := listCodeEncodeNat_length_mono (count_le body values n)
    simp only [encodedListSpace_cons]
    omega
  have project := get_unit 0 (count body values n :: n :: values)
    (2*(encodedListSpace (n::values)+1)) size
  have fit := EvaluatorCodeFits.comp project run
  simp only [List.getElem?_cons_zero,Option.getD_some] at fit
  apply fit.mono
  simp only [coefficient]
  nlinarith

end LeanTrominoes.BoundedArithmetic.Count
