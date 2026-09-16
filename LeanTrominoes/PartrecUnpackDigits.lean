/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BoundedArithmeticLogic
import LeanTrominoes.PartrecFlatIterationUniformSpace

/-! # Unpacking bounded fields into a native evaluator list

A packed word stores a polynomial number of bounded digits. This routine
turns it into native fields without retaining an encoded recursive list.
-/
namespace LeanTrominoes.PackedFields
open Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open BoundedArithmetic BoundedArithmetic.Expr

def pack (base : Nat) : List Nat → Nat
  | [] => 0
  | a::xs => a + base * pack base xs

def step (values : List Nat) : List Nat :=
  [values[0]?.getD 0 / values[1]?.getD 0, values[1]?.getD 0,
    values[0]?.getD 0 % values[1]?.getD 0] ++ values.drop 2

def stepCode : Code :=
  Code.prepend (var 0 / var 1).code (Code.prepend (Code.get 1)
    (Code.prepend (var 0 % var 1).code (Code.drop 2)))

theorem step_eval (values : List Nat) : stepCode.eval values = pure (step values) := by
  simp [stepCode,Code.prepend_eval_eq,Expr.code_eval,step,Part.bind_eq_bind]

theorem step_pack (base a : Nat) (xs acc : List Nat) (ha : a < base) :
    step (pack base (a::xs) :: base :: acc) = pack base xs :: base :: a :: acc := by
  have hp : 0 < base := by omega
  have hd := Nat.add_mul_div_left a (pack base xs) hp
  simp [step,pack,hd,Nat.div_eq_of_lt ha,Nat.mod_eq_of_lt ha]

theorem iterate_pack (base : Nat) (xs acc : List Nat) (bounded : ∀ a ∈ xs, a < base) :
    (step^[xs.length]) (pack base xs :: base :: acc) = 0 :: base :: (xs.reverse ++ acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a xs ih =>
    rw [List.length_cons,Function.iterate_succ_apply,step_pack _ _ _ _ (bounded a (by simp))]
    rw [ih (a::acc) (fun d hd => bounded d (by simp [hd]))]
    simp

def unpackCode : Code := (Code.drop 2).comp (Code.flatIterate stepCode)

theorem unpack_eval (base : Nat) (xs : List Nat) (bounded : ∀ a ∈ xs, a < base) :
    unpackCode.eval [xs.length,pack base xs,base] = pure xs.reverse := by
  have loop := Code.flatIterate_eval stepCode step step_eval xs.length [pack base xs,base]
  rw [iterate_pack base xs [] bounded] at loop
  simp [unpackCode,loop,Part.bind_eq_bind]

/-- Polynomial-bit-size words suffice for a polynomial number of bounded fields. -/
theorem pack_lt_pow (base : Nat) (xs : List Nat) (_positive : 0 < base)
    (bounded : ∀ a ∈ xs, a < base) : pack base xs < base ^ xs.length := by
  induction xs with
  | nil => simp [pack]
  | cons a xs ih =>
    have ha := bounded a (by simp)
    have ht := ih (fun d hd => bounded d (by simp [hd]))
    simp only [pack,List.length_cons,pow_succ]
    nlinarith

end LeanTrominoes.PackedFields
