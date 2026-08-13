/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedSavitchDFSComputability
import LeanTrominoes.PartrecListCode

/-!
# Explicit partial-recursive Savitch fuel program

The generic primitive-recursive compiler proves that the exact Savitch fuel
is computable, but does not expose its evaluator-space behavior.  This module
implements the recurrence with nested flat countdowns.  The live payload
retains only the state count, the previous fuel, and a monotone partial total.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes.FiniteState

attribute [local simp] Part.bind_eq_bind

/-- Increment the third field while preserving the first two fields. -/
def fuelIncrementTotalCode : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      succ.comp (get 2)

def fuelIncrementTotalList (values : List Nat) : List Nat :=
  [values[0]?.getD 0, values[1]?.getD 0,
    values[2]?.getD 0 + 1]

@[simp]
theorem fuelIncrementTotalCode_eval (values : List Nat) :
    fuelIncrementTotalCode.eval values =
      pure (fuelIncrementTotalList values) := by
  simp [fuelIncrementTotalCode, fuelIncrementTotalList]

theorem fuelIncrementTotalList_iterate
    (steps stateCount previous total : Nat) :
    ((fuelIncrementTotalList)^[steps])
        [stateCount, previous, total] =
      [stateCount, previous, total + steps] := by
  induction steps with
  | zero => simp
  | succ steps induction =>
      rw [Function.iterate_succ_apply']
      simp [induction, fuelIncrementTotalList]
      omega

/-- Present the previous fuel as a countdown while preserving the arithmetic
payload behind it. -/
def fuelAddPreviousInputCode : Code :=
  prepend (get 1) <|
    prepend (get 0) <|
      prepend (get 1) (get 2)

@[simp]
theorem fuelAddPreviousInputCode_eval
    (values : List Nat) :
    fuelAddPreviousInputCode.eval values =
      pure [values[1]?.getD 0, values[0]?.getD 0,
        values[1]?.getD 0, values[2]?.getD 0] := by
  simp [fuelAddPreviousInputCode]

/-- Add the previous fuel once to the partial total. -/
def fuelAddPreviousCode : Code :=
  (flatIterate fuelIncrementTotalCode).comp
    fuelAddPreviousInputCode

@[simp]
theorem fuelAddPreviousCode_eval
    (values : List Nat) :
    fuelAddPreviousCode.eval values =
      pure [values[0]?.getD 0, values[1]?.getD 0,
        values[2]?.getD 0 + values[1]?.getD 0] := by
  simp [fuelAddPreviousCode, flatIterate_eval,
    fuelIncrementTotalList_iterate]

/-- Add two to the third field while preserving the first two. -/
def fuelAddTwoCode : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      (addConst 2).comp (get 2)

@[simp]
theorem fuelAddTwoCode_eval
    (values : List Nat) :
    fuelAddTwoCode.eval values =
      pure [values[0]?.getD 0, values[1]?.getD 0,
        values[2]?.getD 0 + 2] := by
  simp [fuelAddTwoCode]

/-- Add `2 * previous + 2` to the partial total. -/
def fuelAddChunkCode : Code :=
  fuelAddTwoCode.comp <|
    fuelAddPreviousCode.comp fuelAddPreviousCode

def fuelAddChunkList (values : List Nat) : List Nat :=
  [values[0]?.getD 0, values[1]?.getD 0,
    values[2]?.getD 0 + (2 * values[1]?.getD 0 + 2)]

@[simp]
theorem fuelAddChunkCode_eval (values : List Nat) :
    fuelAddChunkCode.eval values =
      pure (fuelAddChunkList values) := by
  simp [fuelAddChunkCode, fuelAddChunkList]
  ring

theorem fuelAddChunkList_iterate
    (steps stateCount previous total : Nat) :
    ((fuelAddChunkList)^[steps])
        [stateCount, previous, total] =
      [stateCount, previous,
        total + steps * (2 * previous + 2)] := by
  induction steps with
  | zero => simp
  | succ steps induction =>
      rw [Function.iterate_succ_apply']
      simp [induction, fuelAddChunkList]
      ring

/-- Assemble the multiplication countdown used by one fuel recurrence step. -/
def fuelMultiplyInputCode : Code :=
  prepend (get 0) <|
    prepend (get 0) <|
      prepend (get 1) <|
        one

@[simp]
theorem fuelMultiplyInputCode_eval
    (values : List Nat) :
    fuelMultiplyInputCode.eval values =
      pure [values[0]?.getD 0, values[0]?.getD 0,
        values[1]?.getD 0, 1] := by
  simp [fuelMultiplyInputCode]

/-- Retain the state count and computed recurrence value. -/
def fuelStepOutputCode : Code :=
  prepend (get 0) (get 2)

@[simp]
theorem fuelStepOutputCode_eval
    (values : List Nat) :
    fuelStepOutputCode.eval values =
      pure [values[0]?.getD 0, values[2]?.getD 0] := by
  simp [fuelStepOutputCode]

/-- One step `previous ↦ 1 + stateCount * (2 * previous + 2)` of the exact
fuel recurrence, retaining `stateCount` for the next outer iteration. -/
def fuelStepCode : Code :=
  fuelStepOutputCode.comp <|
    (flatIterate fuelAddChunkCode).comp fuelMultiplyInputCode

def fuelStepList (values : List Nat) : List Nat :=
  [values[0]?.getD 0,
    1 + values[0]?.getD 0 * (2 * values[1]?.getD 0 + 2)]

@[simp]
theorem fuelStepCode_eval (values : List Nat) :
    fuelStepCode.eval values = pure (fuelStepList values) := by
  simp [fuelStepCode, fuelStepList, flatIterate_eval,
    fuelAddChunkList_iterate]

theorem fuelStepList_iterate (stateCount depth : Nat) :
    ((fuelStepList)^[depth]) [stateCount, 1] =
      [stateCount, divideEvalFuel stateCount depth] := by
  induction depth with
  | zero => simp [divideEvalFuel]
  | succ depth induction =>
      rw [Function.iterate_succ_apply']
      simp [induction, fuelStepList, divideEvalFuel]

/-- Assemble the outer depth countdown and initial fuel value. -/
def divideEvalFuelInputCode : Code :=
  prepend (get 1) <|
    prepend (get 0) one

@[simp]
theorem divideEvalFuelInputCode_eval
    (stateCount depth : Nat) :
    divideEvalFuelInputCode.eval [stateCount, depth] =
      pure [depth, stateCount, 1] := by
  simp [divideEvalFuelInputCode]

/-- Two-argument explicit code computing the exact fuel of one Savitch query. -/
def divideEvalFuelCode : Code :=
  (get 1).comp <|
    (flatIterate fuelStepCode).comp divideEvalFuelInputCode

@[simp]
theorem divideEvalFuelCode_eval (stateCount depth : Nat) :
    divideEvalFuelCode.eval [stateCount, depth] =
      pure [divideEvalFuel stateCount depth] := by
  simp [divideEvalFuelCode, flatIterate_eval,
    fuelStepList_iterate]

end Turing.ToPartrec.Code
