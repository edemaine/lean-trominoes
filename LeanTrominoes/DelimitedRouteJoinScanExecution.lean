/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinExecutionSupport
import LeanTrominoes.DelimitedRouteJoinParseSteps

/-! # Input-scanning loops for delimited-route joining -/

noncomputable section

namespace LeanTrominoes.DelimitedRouteJoin

open StateTransition Turing

def scanLeft_evalsInTime (tokens : List Token)
    (tail : List InputSymbol) (data : TapeData)
    (inputEq : data.input =
      tokens.map .left ++ .separator :: tail) :
    EvalsToInTime machine.step (scanLeftCfg data)
      (some (scanRightCfg
        { data with
          input := tail
          prefixReverse := tokens.reverse ++ data.prefixReverse }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_scanLeft_separator data tail (by simpa using inputEq)
      simpa using oneStep step
  | cons token tokens induction =>
      have inputHead : data.input =
          .left token ::
            (tokens.map .left ++ .separator :: tail) := by
        simpa [List.map_cons] using inputEq
      let popped := oneStep
        (step_scanLeft_left data token
          (tokens.map .left ++ .separator :: tail) inputHead)
      let nextData : TapeData :=
        { data with
          input := tokens.map .left ++ .separator :: tail
          prefixReverse := token :: data.prefixReverse }
      let pushed := oneStep
        (step_pushPrefixReverse
          { data with input :=
              tokens.map .left ++ .separator :: tail }
          token)
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

def scanRight_evalsInTime (tokens : List Token) (data : TapeData)
    (inputEq : data.input = tokens.map .right) :
    EvalsToInTime machine.step (scanRightCfg data)
      (some (restorePrefixesCfg
        { data with
          input := []
          suffixReverse := tokens.reverse ++ data.suffixReverse }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_scanRight_nil data (by simpa using inputEq)
      simpa using oneStep step
  | cons token tokens induction =>
      have inputHead : data.input =
          .right token :: tokens.map .right := by
        simpa [List.map_cons] using inputEq
      let popped := oneStep
        (step_scanRight_right data token (tokens.map .right) inputHead)
      let nextData : TapeData :=
        { data with
          input := tokens.map .right
          suffixReverse := token :: data.suffixReverse }
      let pushed := oneStep
        (step_pushSuffixReverse
          { data with input := tokens.map .right } token)
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end LeanTrominoes.DelimitedRouteJoin

end
