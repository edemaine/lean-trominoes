/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterParseSteps

/-! # Complete parsing of paired unary streams -/

noncomputable section

namespace LeanTrominoes
namespace UnarySuccessorEqualityFilterMachine

open StateTransition Turing

private def oneStep {before after : machine.Cfg}
    (step : machine.step before = some after) :
    EvalsToInTime machine.step before (some after) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    exact step
  steps_le_m := Nat.le_refl 1

def scanLeft_evalsInTime (tokens : List UnarySymbol)
    (tail : List InputSymbol) (data : TapeData)
    (inputEq : data.input = tokens.map .left ++ .separator :: tail) :
    EvalsToInTime machine.step (scanLeftCfg data)
      (some (scanRightCfg
        { data with
          input := tail
          rankReverse := tokens.reverse ++ data.rankReverse }))
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
          rankReverse := symbol :: data.rankReverse }
      let pushed := oneStep
        (step_pushRankReverse
          { data with input := tokens.map .left ++ .separator :: tail }
          symbol)
      have restInput : nextData.input =
          tokens.map .left ++ .separator :: tail := rfl
      let rest := induction nextData restInput
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

def scanRight_evalsInTime (tokens : List UnarySymbol) (data : TapeData)
    (inputEq : data.input = tokens.map .right) :
    EvalsToInTime machine.step (scanRightCfg data)
      (some (restoreRanksCfg
        { data with
          input := []
          sizeReverse := tokens.reverse ++ data.sizeReverse }))
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
          sizeReverse := symbol :: data.sizeReverse }
      let pushed := oneStep
        (step_pushSizeReverse { data with input := tokens.map .right } symbol)
      have restInput : nextData.input = tokens.map .right := rfl
      let rest := induction nextData restInput
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

def restoreRanks_evalsInTime (tokens : List UnarySymbol)
    (data : TapeData) (reverseEq : data.rankReverse = tokens) :
    EvalsToInTime machine.step (restoreRanksCfg data)
      (some (restoreSizesCfg
        { data with
          rankReverse := []
          ranks := tokens.reverse ++ data.ranks }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_restoreRanks_nil data reverseEq
      simpa using oneStep step
  | cons symbol tokens induction =>
      let popped := oneStep
        (step_restoreRanks_cons data symbol tokens reverseEq)
      let nextData : TapeData :=
        { data with
          rankReverse := tokens
          ranks := symbol :: data.ranks }
      let pushed := oneStep
        (step_pushRank { data with rankReverse := tokens } symbol)
      have nextEq : nextData.rankReverse = tokens := rfl
      let rest := induction nextData nextEq
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

def restoreSizes_evalsInTime (tokens : List UnarySymbol)
    (data : TapeData) (reverseEq : data.sizeReverse = tokens) :
    EvalsToInTime machine.step (restoreSizesCfg data)
      (some (scanRankCfg
        { data with
          sizeReverse := []
          sizes := tokens.reverse ++ data.sizes }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_restoreSizes_nil data reverseEq
      simpa using oneStep step
  | cons symbol tokens induction =>
      let popped := oneStep
        (step_restoreSizes_cons data symbol tokens reverseEq)
      let nextData : TapeData :=
        { data with
          sizeReverse := tokens
          sizes := symbol :: data.sizes }
      let pushed := oneStep
        (step_pushSize { data with sizeReverse := tokens } symbol)
      have nextEq : nextData.sizeReverse = tokens := rfl
      let rest := induction nextData nextEq
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes
