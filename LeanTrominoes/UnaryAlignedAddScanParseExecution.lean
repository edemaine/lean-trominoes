/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddExecutionSupport
import LeanTrominoes.UnaryAlignedAddParseLeftTailSteps
import LeanTrominoes.UnaryAlignedAddParseRightSteps
import LeanTrominoes.UnaryAlignedAddParseSteps

/-! # Input-scanning loops for aligned unary addition -/

noncomputable section

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open StateTransition Turing

def scanLeft_evalsInTime (tokens : List UnarySymbol)
    (tail : List InputSymbol) (data : TapeData)
    (inputEq : data.input = tokens.map .left ++ .separator :: tail) :
    EvalsToInTime machine.step (scanLeftCfg data)
      (some (scanRightCfg
        { data with
          input := tail
          firstReverse := tokens.reverse ++ data.firstReverse }))
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
          firstReverse := symbol :: data.firstReverse }
      let pushed := oneStep
        (step_pushFirstReverse
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
      (some (restoreFirstsCfg
        { data with
          input := []
          secondReverse := tokens.reverse ++ data.secondReverse }))
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
          secondReverse := symbol :: data.secondReverse }
      let pushed := oneStep
        (step_pushSecondReverse
          { data with input := tokens.map .right } symbol)
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end UnaryAlignedAddMachine
end LeanTrominoes
