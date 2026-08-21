/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupParseSteps

/-! # Complete parsing loops for last-true unary lookup -/

noncomputable section

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

open StateTransition Turing

private def oneStep {before after : machine.Cfg}
    (step : machine.step before = some after) :
    EvalsToInTime machine.step before (some after) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    exact step
  steps_le_m := Nat.le_refl 1

def scanLeft_evalsInTime (tokens : List RowSymbol)
    (tail : List InputSymbol) (data : TapeData)
    (inputEq : data.input = tokens.map .left ++ .separator :: tail) :
    EvalsToInTime machine.step (scanLeftCfg data)
      (some (scanRightCfg
        { data with
          input := tail
          rowsReverse := tokens.reverse ++ data.rowsReverse }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_scanLeft_separator data tail (by simpa using inputEq)
      simpa using oneStep step
  | cons symbol tokens induction =>
      have inputHead : data.input =
          .left symbol :: (tokens.map .left ++ .separator :: tail) := by
        simpa [List.map_cons] using inputEq
      let popped := oneStep
        (step_scanLeft_left data symbol
          (tokens.map .left ++ .separator :: tail) inputHead)
      let nextData : TapeData :=
        { data with
          input := tokens.map .left ++ .separator :: tail
          rowsReverse := symbol :: data.rowsReverse }
      let pushed := oneStep
        (step_pushRowReverse
          { data with input := tokens.map .left ++ .separator :: tail }
          symbol)
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

def scanRight_evalsInTime (tokens : List UnarySymbol) (data : TapeData)
    (inputEq : data.input = tokens.map .right) :
    EvalsToInTime machine.step (scanRightCfg data)
      (some (restoreRowsCfg
        { data with
          input := []
          valuesReverse := tokens.reverse ++ data.valuesReverse }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_scanRight_nil data (by simpa using inputEq)
      simpa using oneStep step
  | cons symbol tokens induction =>
      have inputHead : data.input = .right symbol :: tokens.map .right := by
        simpa [List.map_cons] using inputEq
      let popped := oneStep
        (step_scanRight_right data symbol (tokens.map .right) inputHead)
      let nextData : TapeData :=
        { data with
          input := tokens.map .right
          valuesReverse := symbol :: data.valuesReverse }
      let pushed := oneStep
        (step_pushValueReverse { data with input := tokens.map .right } symbol)
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

def restoreRows_evalsInTime (tokens : List RowSymbol)
    (data : TapeData) (reverseEq : data.rowsReverse = tokens) :
    EvalsToInTime machine.step (restoreRowsCfg data)
      (some (restoreInitialValuesCfg
        { data with
          rowsReverse := []
          rows := tokens.reverse ++ data.rows }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_restoreRows_nil data reverseEq
      simpa using oneStep step
  | cons symbol tokens induction =>
      let popped := oneStep
        (step_restoreRows_cons data symbol tokens reverseEq)
      let nextData : TapeData :=
        { data with
          rowsReverse := tokens
          rows := symbol :: data.rows }
      let pushed := oneStep
        (step_pushRow { data with rowsReverse := tokens } symbol)
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

def restoreInitialValues_evalsInTime (tokens : List UnarySymbol)
    (data : TapeData) (reverseEq : data.valuesReverse = tokens) :
    EvalsToInTime machine.step (restoreInitialValuesCfg data)
      (some (scanRowsCfg
        { data with
          valuesReverse := []
          values := tokens.reverse ++ data.values }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_restoreInitialValues_nil data reverseEq
      simpa using oneStep step
  | cons symbol tokens induction =>
      let popped := oneStep
        (step_restoreInitialValues_cons data symbol tokens reverseEq)
      let nextData : TapeData :=
        { data with
          valuesReverse := tokens
          values := symbol :: data.values }
      let pushed := oneStep
        (step_pushInitialValue { data with valuesReverse := tokens } symbol)
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
