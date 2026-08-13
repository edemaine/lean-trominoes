/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecNatCompare

/-!
# Explicit quotient-and-remainder code

State-index decoding needs division by the input period, while frontier-word
decoding repeatedly divides by the constant base nine.  This module supplies
one binary program for both uses.  Its flat countdown retains only the
quotient, remainder, and divisor, so the corresponding evaluator certificate
can reuse one small payload even when the dividend is numerically large.
-/

namespace Turing.ToPartrec.Code

attribute [local simp] Part.bind_eq_bind

/-- One long-division step on `[quotient, remainder, divisor]`.  The
zero-divisor branch follows Lean's natural-number conventions:
`number / 0 = 0` and `number % 0 = number`. -/
def divisionListStep (values : List Nat) : List Nat :=
  let quotient := values[0]?.getD 0
  let remainder := values[1]?.getD 0
  let divisor := values[2]?.getD 0
  if divisor = 0 then
    [quotient, remainder + 1, divisor]
  else if remainder + 1 < divisor then
    [quotient, remainder + 1, divisor]
  else
    [quotient + 1, 0, divisor]

def divisionAdvanceCode : Code :=
  prepend (get 0) <|
    prepend (succ.comp (get 1)) (get 2)

def divisionResetCode : Code :=
  prepend (succ.comp (get 0)) <|
    prepend zero (get 2)

def divisionBelowCode : Code :=
  natLtCode.comp <|
    prepend (succ.comp (get 1)) (get 2)

/-- Explicit list code for one quotient/remainder update. -/
def divisionListStepCode : Code :=
  branchZero (get 2)
    divisionAdvanceCode <|
    branchZero divisionBelowCode
      divisionResetCode divisionAdvanceCode

@[simp]
theorem divisionListStepCode_eval (values : List Nat) :
    divisionListStepCode.eval values =
      pure (divisionListStep values) := by
  let quotient := values[0]?.getD 0
  let remainder := values[1]?.getD 0
  let divisor := values[2]?.getD 0
  by_cases divisorZero : divisor = 0
  · have evaluated :=
      branchZero_eval_zero_at
        (get 2) divisionAdvanceCode
        (branchZero divisionBelowCode
          divisionResetCode divisionAdvanceCode)
        values divisor (get_eval 2 values)
        [quotient, remainder + 1, divisor]
        (by
          simp [divisionAdvanceCode, quotient,
            remainder, divisor])
        divisorZero
    simpa [divisionListStepCode, divisionListStep,
      quotient, remainder, divisor, divisorZero] using evaluated
  · have divisorPositive : 0 < divisor :=
      Nat.pos_of_ne_zero divisorZero
    by_cases below : remainder + 1 < divisor
    · have inner :=
        branchZero_eval_succ_at
          divisionBelowCode divisionResetCode divisionAdvanceCode
          values 1
          (by
            simp [divisionBelowCode, below, remainder, divisor])
          [quotient, remainder + 1, divisor]
          (by
            simp [divisionAdvanceCode, quotient,
              remainder, divisor])
          (by omega)
      have evaluated :=
        branchZero_eval_succ_at
          (get 2) divisionAdvanceCode
          (branchZero divisionBelowCode
            divisionResetCode divisionAdvanceCode)
          values divisor (get_eval 2 values)
          [quotient, remainder + 1, divisor]
          inner divisorPositive
      simpa [divisionListStepCode, divisionListStep,
        quotient, remainder, divisor, divisorZero, below] using
        evaluated
    · have inner :=
        branchZero_eval_zero_at
          divisionBelowCode divisionResetCode divisionAdvanceCode
          values 0
          (by
            simp [divisionBelowCode, below, remainder, divisor])
          [quotient + 1, 0, divisor]
          (by
            simp [divisionResetCode, quotient, divisor])
          rfl
      have evaluated :=
        branchZero_eval_succ_at
          (get 2) divisionAdvanceCode
          (branchZero divisionBelowCode
            divisionResetCode divisionAdvanceCode)
          values divisor (get_eval 2 values)
          [quotient + 1, 0, divisor]
          inner divisorPositive
      simpa [divisionListStepCode, divisionListStep,
        quotient, remainder, divisor, divisorZero, below] using
        evaluated

/-- Mathematical state mirrored by the flat list program. -/
def divisionProcess (divisor : Nat) :
    Nat → Nat × Nat
  | 0 => (0, 0)
  | steps + 1 =>
      let state := divisionProcess divisor steps
      if divisor = 0 then
        (state.1, state.2 + 1)
      else if state.2 + 1 < divisor then
        (state.1, state.2 + 1)
      else
        (state.1 + 1, 0)

theorem divisionListStep_iterate_process
    (steps divisor : Nat) :
    (divisionListStep^[steps]) [0, 0, divisor] =
      [(divisionProcess divisor steps).1,
        (divisionProcess divisor steps).2, divisor] := by
  induction steps with
  | zero =>
      rfl
  | succ steps induction =>
      rw [Function.iterate_succ_apply', induction]
      by_cases divisorZero : divisor = 0 <;>
        by_cases below :
          (divisionProcess divisor steps).2 + 1 < divisor <;>
        simp [divisionListStep, divisionProcess,
          divisorZero, below]

theorem divisionProcess_invariant
    (steps divisor : Nat) :
    let state := divisionProcess divisor steps
    steps = state.1 * divisor + state.2 ∧
      (divisor = 0 ∨ state.2 < divisor) := by
  induction steps with
  | zero =>
      simp [divisionProcess, Nat.eq_zero_or_pos divisor]
  | succ steps induction =>
      change
        steps =
            (divisionProcess divisor steps).1 * divisor +
              (divisionProcess divisor steps).2 ∧
          (divisor = 0 ∨
            (divisionProcess divisor steps).2 < divisor)
        at induction
      by_cases divisorZero : divisor = 0
      · simp [divisionProcess, divisorZero] at induction ⊢
        omega
      · have remainderBound :
          (divisionProcess divisor steps).2 < divisor :=
          induction.2.resolve_left divisorZero
        by_cases below :
            (divisionProcess divisor steps).2 + 1 < divisor
        · simp [divisionProcess, divisorZero, below]
          omega
        · have reachesDivisor :
            (divisionProcess divisor steps).2 + 1 = divisor := by
            omega
          simp [divisionProcess, divisorZero, below]
          constructor
          · calc
              steps + 1 =
                  (divisionProcess divisor steps).1 * divisor +
                    (divisionProcess divisor steps).2 + 1 := by
                omega
              _ = ((divisionProcess divisor steps).1 + 1) *
                    divisor := by
                rw [Nat.add_mul]
                omega
          · exact Nat.pos_of_ne_zero divisorZero

@[simp]
theorem divisionProcess_zero (number : Nat) :
    divisionProcess 0 number = (0, number) := by
  induction number with
  | zero =>
      rfl
  | succ number induction =>
      simp [divisionProcess, induction]

theorem divisionProcess_eq_div_mod
    (number divisor : Nat) :
    divisionProcess divisor number =
      (number / divisor, number % divisor) := by
  have invariant := divisionProcess_invariant number divisor
  let state := divisionProcess divisor number
  change
    number = state.1 * divisor + state.2 ∧
      (divisor = 0 ∨ state.2 < divisor) at invariant
  by_cases divisorZero : divisor = 0
  · subst divisor
    simp
  · have divisorPositive : 0 < divisor :=
      Nat.pos_of_ne_zero divisorZero
    have remainderBound : state.2 < divisor :=
      invariant.2.resolve_left divisorZero
    have remainderEq : number % divisor = state.2 := by
      rw [invariant.1]
      simp [Nat.add_mod,
        Nat.mod_eq_of_lt remainderBound]
    have quotientEq : number / divisor = state.1 := by
      rw [invariant.1]
      calc
        (state.1 * divisor + state.2) / divisor =
            (state.2 + divisor * state.1) / divisor := by
          rw [Nat.mul_comm state.1 divisor, Nat.add_comm]
        _ = state.2 / divisor + state.1 :=
          Nat.add_mul_div_left _ _ divisorPositive
        _ = state.1 := by
          rw [Nat.div_eq_of_lt remainderBound]
          simp
    apply Prod.ext
    · exact quotientEq.symm
    · exact remainderEq.symm

/-- Assemble `[number, 0, 0, divisor]` for the flat loop. -/
def divisionInputCode : Code :=
  prepend (get 0) <|
    prepend zero <|
      prepend zero (get 1)

@[simp]
theorem divisionInputCode_eval
    (number divisor : Nat) :
    divisionInputCode.eval [number, divisor] =
      pure [number, 0, 0, divisor] := by
  simp [divisionInputCode]

/-- Binary code returning `[number / divisor, number % divisor]`. -/
def divisionCode : Code :=
  (prepend (get 0) (get 1)).comp <|
    (flatIterate divisionListStepCode).comp divisionInputCode

@[simp]
theorem divisionCode_eval (number divisor : Nat) :
    divisionCode.eval [number, divisor] =
      pure [number / divisor, number % divisor] := by
  simp [divisionCode,
    flatIterate_eval divisionListStepCode divisionListStep
      divisionListStepCode_eval,
    divisionListStep_iterate_process,
    divisionProcess_eq_div_mod]

end Turing.ToPartrec.Code
