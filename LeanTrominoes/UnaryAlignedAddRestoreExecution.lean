/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddExecutionSupport
import LeanTrominoes.UnaryAlignedAddRestoreSteps

/-! # Stack-restoration loops for aligned unary addition -/

noncomputable section

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open StateTransition Turing

def restoreFirsts_evalsInTime (tokens : List UnarySymbol)
    (data : TapeData) (reverseEq : data.firstReverse = tokens) :
    EvalsToInTime machine.step (restoreFirstsCfg data)
      (some (restoreSecondsCfg
        { data with
          firstReverse := []
          firsts := tokens.reverse ++ data.firsts }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_restoreFirsts_nil data reverseEq
      simpa using oneStep step
  | cons symbol tokens induction =>
      let popped := oneStep
        (step_restoreFirsts_cons data symbol tokens reverseEq)
      let pushed := oneStep
        (step_pushFirst { data with firstReverse := tokens } symbol)
      let nextData : TapeData :=
        { data with
          firstReverse := tokens
          firsts := symbol :: data.firsts }
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

def restoreSeconds_evalsInTime (tokens : List UnarySymbol)
    (data : TapeData) (reverseEq : data.secondReverse = tokens) :
    EvalsToInTime machine.step (restoreSecondsCfg data)
      (some (scanFirstFieldCfg
        { data with
          secondReverse := []
          seconds := tokens.reverse ++ data.seconds }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_restoreSeconds_nil data reverseEq
      simpa using oneStep step
  | cons symbol tokens induction =>
      let popped := oneStep
        (step_restoreSeconds_cons data symbol tokens reverseEq)
      let pushed := oneStep
        (step_pushSecond { data with secondReverse := tokens } symbol)
      let nextData : TapeData :=
        { data with
          secondReverse := tokens
          seconds := symbol :: data.seconds }
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end UnaryAlignedAddMachine
end LeanTrominoes
