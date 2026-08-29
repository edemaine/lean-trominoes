/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinExecutionSupport
import LeanTrominoes.DelimitedRouteJoinRestoreSteps

/-! # Stack-restoration loops for delimited-route joining -/

noncomputable section

namespace LeanTrominoes.DelimitedRouteJoin

open StateTransition Turing

def restorePrefixes_evalsInTime (tokens : List Token)
    (data : TapeData) (reverseEq : data.prefixReverse = tokens) :
    EvalsToInTime machine.step (restorePrefixesCfg data)
      (some (restoreSuffixesCfg
        { data with
          prefixReverse := []
          prefixes := tokens.reverse ++ data.prefixes }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_restorePrefixes_nil data reverseEq
      simpa using oneStep step
  | cons token tokens induction =>
      let popped := oneStep
        (step_restorePrefixes_cons data token tokens reverseEq)
      let pushed := oneStep
        (step_pushPrefix
          { data with prefixReverse := tokens } token)
      let nextData : TapeData :=
        { data with
          prefixReverse := tokens
          prefixes := token :: data.prefixes }
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

def restoreSuffixes_evalsInTime (tokens : List Token)
    (data : TapeData) (reverseEq : data.suffixReverse = tokens) :
    EvalsToInTime machine.step (restoreSuffixesCfg data)
      (some (scanPrefixCfg
        { data with
          suffixReverse := []
          suffixes := tokens.reverse ++ data.suffixes }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_restoreSuffixes_nil data reverseEq
      simpa using oneStep step
  | cons token tokens induction =>
      let popped := oneStep
        (step_restoreSuffixes_cons data token tokens reverseEq)
      let pushed := oneStep
        (step_pushSuffix
          { data with suffixReverse := tokens } token)
      let nextData : TapeData :=
        { data with
          suffixReverse := tokens
          suffixes := token :: data.suffixes }
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end LeanTrominoes.DelimitedRouteJoin

end
