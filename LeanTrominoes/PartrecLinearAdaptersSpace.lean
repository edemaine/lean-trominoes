/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecListCodeSpace
import Mathlib.Tactic.Linarith

/-! # Linear-space composition rules for flat-list adapters -/

namespace Turing.PartrecToTM2.EvaluatorCodeFits
open ToPartrec

theorem get_linear (index : Nat) (values : List Nat) :
    EvaluatorCodeFits (Code.get index) values [values[index]?.getD 0]
      ((10000*(index+1))*(encodedListSpace values+1)) :=
  (get index values).mono (listCodeGetCost_le_linear index values)

theorem drop_linear (index : Nat) (values : List Nat) :
    EvaluatorCodeFits (Code.drop index) values (values.drop index)
      ((10000*(index+1))*(encodedListSpace values+1)) := by
  apply (drop index values).mono
  have h := listCodeGetCost_le_linear index values
  simp only [getCost] at h
  omega

theorem prepend_linear {field rest : Code} {values : List Nat} {value : Nat} {output : List Nat}
    {a b : Nat}
    (first : EvaluatorCodeFits field values [value] (a*(encodedListSpace values+1)))
    (last : EvaluatorCodeFits rest values output (b*(encodedListSpace values+1))) :
    EvaluatorCodeFits (Code.prepend field rest) values (value :: output)
      ((4*(a+b+1))*(encodedListSpace values+1)) := by
  apply (prepend first last).mono
  have hf := first.output_space
  have hr := last.output_space
  simp only [prependCost,encodedListSpace_cons,encodedListSpace_nil,List.headI_cons] at hf hr ⊢
  nlinarith

theorem comp_linear {outer inner : Code} {values middle output : List Nat} {a b : Nat}
    (last : EvaluatorCodeFits outer middle output (b*(encodedListSpace middle+1)))
    (first : EvaluatorCodeFits inner values middle (a*(encodedListSpace values+1))) :
    EvaluatorCodeFits (outer.comp inner) values output
      ((b*(a+1)+a)*(encodedListSpace values+1)) := by
  apply (comp last first).mono
  have hm := first.output_space
  nlinarith [Nat.mul_le_mul_left b hm]


theorem prepend_unit {field rest : Code} {values : List Nat} {value : Nat} {output : List Nat}
    {a b unit : Nat} (hu : encodedListSpace values+1 ≤ unit)
    (first : EvaluatorCodeFits field values [value] (a*unit))
    (last : EvaluatorCodeFits rest values output (b*unit)) :
    EvaluatorCodeFits (Code.prepend field rest) values (value :: output) ((4*(a+b+1))*unit) := by
  apply (prepend first last).mono
  have hf := first.output_space
  have hr := last.output_space
  simp only [prependCost,encodedListSpace_cons,encodedListSpace_nil,List.headI_cons] at hf hr ⊢
  nlinarith

theorem get_unit (index : Nat) (values : List Nat) (unit : Nat) (hu : encodedListSpace values+1 ≤ unit) :
    EvaluatorCodeFits (Code.get index) values [values[index]?.getD 0] ((10000*(index+1))*unit) :=
  (get_linear index values).mono (Nat.mul_le_mul_left _ hu)

theorem drop_unit (index : Nat) (values : List Nat) (unit : Nat) (hu : encodedListSpace values+1 ≤ unit) :
    EvaluatorCodeFits (Code.drop index) values (values.drop index) ((10000*(index+1))*unit) :=
  (drop_linear index values).mono (Nat.mul_le_mul_left _ hu)

theorem zero_unit (values : List Nat) (unit : Nat) (hu : encodedListSpace values+1 ≤ unit) :
    EvaluatorCodeFits Code.zero values [0] (10000*unit) := by
  apply (zero values).mono
  have h := listCodeZeroCost_le_linear values
  omega

end Turing.PartrecToTM2.EvaluatorCodeFits
