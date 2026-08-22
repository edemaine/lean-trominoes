/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationExecutionSupport
import LeanTrominoes.UnaryBlockRightRotationParsingSteps

/-! # Stack-restoration loops for unary block right rotation -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def restoreSizes_evalsInTime (tokens : List UnarySymbol)
    (data : TapeData) (reverseEq : data.sizesReverse = tokens) :
    EvalsToInTime machine.step (restoreSizesCfg data)
      (some (restoreStartsCfg
        { data with
          sizesReverse := []
          sizes := tokens.reverse ++ data.sizes }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_restoreSizes_nil data reverseEq
      simpa using oneStep step
  | cons symbol tokens induction =>
      let popped := oneStep
        (step_restoreSizes_cons data symbol tokens reverseEq)
      let pushed := oneStep
        (step_pushSize { data with sizesReverse := tokens } symbol)
      let nextData : TapeData :=
        { data with
          sizesReverse := tokens
          sizes := symbol :: data.sizes }
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

def restoreStarts_evalsInTime (tokens : List UnarySymbol)
    (data : TapeData) (reverseEq : data.startsReverse = tokens) :
    EvalsToInTime machine.step (restoreStartsCfg data)
      (some (scanSizeFieldCfg
        { data with
          startsReverse := []
          starts := tokens.reverse ++ data.starts }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_restoreStarts_nil data reverseEq
      simpa using oneStep step
  | cons symbol tokens induction =>
      let popped := oneStep
        (step_restoreStarts_cons data symbol tokens reverseEq)
      let pushed := oneStep
        (step_pushStart { data with startsReverse := tokens } symbol)
      let nextData : TapeData :=
        { data with
          startsReverse := tokens
          starts := symbol :: data.starts }
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end LeanTrominoes.UnaryBlockRightRotationMachine

end
