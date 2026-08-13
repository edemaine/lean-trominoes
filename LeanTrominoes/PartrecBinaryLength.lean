/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EncodingLengthComputability
import LeanTrominoes.PartrecListCode

/-!
# Explicit partial-recursive binary-length program

The generic `codeOfPrimrec` selector proves only extensional correctness and
does not expose any evaluator-space bound.  This module instead builds the
binary natural-length routine from the project's flat tail-recursive loop.

Division by two is implemented by scanning a countdown while retaining only
a quotient and one parity bit.  The outer length loop repeatedly applies that
division and increments a counter.  Both loops may take very long, but their
live list payloads contain only the original fuel, a shrinking quotient, and
constant-many counters.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes.Computability

attribute [local simp] Part.bind_eq_bind

private theorem getD_zero_eq_headI (values : List Nat) :
    values[0]?.getD 0 = values.headI := by
  cases values <;> rfl

private theorem getD_one_eq_tail_headI (values : List Nat) :
    values[1]?.getD 0 = values.tail.headI := by
  cases values with
  | nil => rfl
  | cons head tail =>
      cases tail <;> rfl

/-- Toggle a parity bit, incrementing the quotient after every second
iteration. -/
def binaryDiv2ListStep (values : List Nat) : List Nat :=
  if values[1]?.getD 0 = 0 then
    [values.headI, 1]
  else
    [values.headI.succ, 0]

/-- Explicit list code for `binaryDiv2ListStep`. -/
def binaryDiv2ListStepCode : Code :=
  branchZero (get 1)
    (prepend (get 0) (prepend one nil))
    (prepend (succ.comp (get 0)) (prepend zero nil))

@[simp]
theorem binaryDiv2ListStepCode_eval (values : List Nat) :
    binaryDiv2ListStepCode.eval values =
      pure (binaryDiv2ListStep values) := by
  unfold binaryDiv2ListStepCode
  by_cases parityZero : values[1]?.getD 0 = 0
  · have evaluated :=
      branchZero_eval_zero_at
      (get 1)
      (prepend (get 0) (prepend one nil))
      (prepend (succ.comp (get 0)) (prepend zero nil))
      values (values[1]?.getD 0)
      (get_eval 1 values)
      [values.headI, 1] (by
        simp [getD_zero_eq_headI]) parityZero
    simpa [binaryDiv2ListStep, parityZero] using evaluated
  · have evaluated :=
      branchZero_eval_succ_at
      (get 1)
      (prepend (get 0) (prepend one nil))
      (prepend (succ.comp (get 0)) (prepend zero nil))
      values (values[1]?.getD 0)
      (get_eval 1 values)
      [values.headI.succ, 0] (by
        simp [getD_zero_eq_headI])
      (Nat.pos_of_ne_zero parityZero)
    simpa [binaryDiv2ListStep, parityZero] using evaluated

/-- Iterating the quotient/parity step computes the binary quotient and low
bit of the iteration count. -/
theorem binaryDiv2ListStep_iterate (number : Nat) :
    (binaryDiv2ListStep^[number]) [0, 0] =
      [number.div2, number.bodd.toNat] := by
  induction number with
  | zero =>
      rfl
  | succ number induction =>
      rw [Function.iterate_succ_apply', induction]
      cases parity : number.bodd <;>
        simp [binaryDiv2ListStep, parity, Nat.div2_succ,
          Nat.bodd_succ]

/-- Build the flat countdown input `[number, quotient, parity]`. -/
def binaryDiv2InputCode : Code :=
  prepend (get 0) <|
    prepend zero <|
      prepend zero nil

@[simp]
theorem binaryDiv2InputCode_eval (values : List Nat) :
    binaryDiv2InputCode.eval values =
      pure [values.headI, 0, 0] := by
  simp [binaryDiv2InputCode, getD_zero_eq_headI]

/-- Explicit unary code for natural-number division by two. -/
def binaryDiv2Code : Code :=
  (get 0).comp <|
    (flatIterate binaryDiv2ListStepCode).comp
      binaryDiv2InputCode

@[simp]
theorem binaryDiv2Code_eval (number : Nat) :
    binaryDiv2Code.eval [number] = pure [number.div2] := by
  simp [binaryDiv2Code,
    flatIterate_eval binaryDiv2ListStepCode binaryDiv2ListStep,
    binaryDiv2ListStep_iterate]

/-- One list-shaped binary-length step on `[remaining, count]`. -/
def binaryLengthListStep (values : List Nat) : List Nat :=
  if values.headI = 0 then
    values
  else
    [values.headI.div2, values.tail.headI.succ]

/-- Explicit code for `binaryLengthListStep`. -/
def binaryLengthListStepCode : Code :=
  branchZero (get 0) id <|
    prepend (binaryDiv2Code.comp (get 0)) <|
      prepend (succ.comp (get 1)) nil

@[simp]
theorem binaryLengthListStepCode_eval (values : List Nat) :
    binaryLengthListStepCode.eval values =
      pure (binaryLengthListStep values) := by
  unfold binaryLengthListStepCode
  by_cases remainingZero : values.headI = 0
  · have evaluated :=
      branchZero_eval_zero_at
      (get 0) id
      (prepend (binaryDiv2Code.comp (get 0))
        (prepend (succ.comp (get 1)) nil))
      values values.headI
      (by simp [getD_zero_eq_headI])
      values (by simp) remainingZero
    simpa [binaryLengthListStep, remainingZero] using evaluated
  · have evaluated :=
      branchZero_eval_succ_at
      (get 0) id
      (prepend (binaryDiv2Code.comp (get 0))
        (prepend (succ.comp (get 1)) nil))
      values values.headI
      (by simp [getD_zero_eq_headI])
      [values.headI.div2, values.tail.headI.succ]
      (by simp [getD_zero_eq_headI, getD_one_eq_tail_headI])
      (Nat.pos_of_ne_zero remainingZero)
    simpa [binaryLengthListStep, remainingZero] using evaluated

theorem binaryLengthListStep_pair (state : Nat × Nat) :
    binaryLengthListStep [state.1, state.2] =
      [binaryEncodingLengthStep state |>.1,
        binaryEncodingLengthStep state |>.2] := by
  by_cases zero : state.1 = 0 <;>
    simp [binaryLengthListStep, binaryEncodingLengthStep, zero]

/-- The list-shaped loop exactly represents iteration of the pair-valued
length state. -/
theorem binaryLengthListStep_iterate
    (steps : Nat) (state : Nat × Nat) :
    (binaryLengthListStep^[steps]) [state.1, state.2] =
      [((binaryEncodingLengthStep^[steps]) state).1,
        ((binaryEncodingLengthStep^[steps]) state).2] := by
  induction steps generalizing state with
  | zero =>
      rfl
  | succ steps induction =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        induction, binaryLengthListStep_pair]

/-- Build the flat countdown input `[number, remaining, count]`. -/
def binaryEncodingLengthInputCode : Code :=
  prepend (get 0) <|
    prepend (get 0) <|
      prepend zero nil

@[simp]
theorem binaryEncodingLengthInputCode_eval (values : List Nat) :
    binaryEncodingLengthInputCode.eval values =
      pure [values.headI, values.headI, 0] := by
  simp [binaryEncodingLengthInputCode, getD_zero_eq_headI]

/-- Explicit unary program computing the length of Mathlib's little-endian
binary encoding of a natural number. -/
def binaryEncodingLengthCode : Code :=
  (get 1).comp <|
    (flatIterate binaryLengthListStepCode).comp
      binaryEncodingLengthInputCode

@[simp]
theorem binaryEncodingLengthCode_eval (number : Nat) :
    binaryEncodingLengthCode.eval [number] =
      pure [binaryEncodingLength number] := by
  simp [binaryEncodingLengthCode,
    flatIterate_eval binaryLengthListStepCode binaryLengthListStep
      binaryLengthListStepCode_eval,
    binaryLengthListStep_iterate number (number, 0),
    binaryEncodingLength]

/-- Singleton-list semantics of adding a fixed increment. -/
def addConstListStep (increment : Nat) (values : List Nat) :
    List Nat :=
  [values.headI + increment]

@[simp]
theorem addConstListStepCode_eval
    (increment : Nat) (values : List Nat) :
    (addConst increment).eval values =
      pure (addConstListStep increment values) := by
  simp [addConstListStep]

theorem addConstListStep_iterate
    (increment steps value : Nat) :
    ((addConstListStep increment)^[steps]) [value] =
      [value + steps * increment] := by
  induction steps with
  | zero =>
      simp
  | succ steps induction =>
      rw [Function.iterate_succ_apply', induction]
      simp [addConstListStep]
      ring

/-- Assemble `[binary length, offset]` for a flat affine loop. -/
def binaryLengthAffineInputCode (offset : Nat) : Code :=
  prepend binaryEncodingLengthCode <|
    prepend (numeral offset) nil

@[simp]
theorem binaryLengthAffineInputCode_eval
    (offset number : Nat) :
    (binaryLengthAffineInputCode offset).eval [number] =
      pure [binaryEncodingLength number, offset] := by
  simp [binaryLengthAffineInputCode]

/-- Explicit unary code for
`offset + multiplier * binaryEncodingLength number`. -/
def binaryLengthAffineCode (multiplier offset : Nat) : Code :=
  (flatIterate (addConst multiplier)).comp
    (binaryLengthAffineInputCode offset)

@[simp]
theorem binaryLengthAffineCode_eval
    (multiplier offset number : Nat) :
    (binaryLengthAffineCode multiplier offset).eval [number] =
      pure [offset + multiplier * binaryEncodingLength number] := by
  simp [binaryLengthAffineCode,
    flatIterate_eval (addConst multiplier)
      (addConstListStep multiplier)
      (addConstListStepCode_eval multiplier),
    addConstListStep_iterate]
  ring

end Turing.ToPartrec.Code
