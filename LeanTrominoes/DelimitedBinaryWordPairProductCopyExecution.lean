/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductSetupSteps

/-! # Input-copy execution for the binary-word product machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

def copyInput_evalsInTime (tokens : List WordToken) (data : TapeData)
    (inputEq : data.input = tokens) :
    EvalsToInTime (TM2.step program) (copyInputCfg data)
      (some (duplicateCfg
        { data with
          input := []
          reverse := tokens.reverse ++ data.reverse }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep (step_copyInput_nil data inputEq)
      convert step using 1 <;> simp
  | cons token tokens induction =>
      let nextData :=
        { data with
          input := tokens
          reverse := token :: data.reverse }
      have first := oneStep
        (step_copyInput_cons data token tokens inputEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (copyInputCfg data) (copyInputCfg nextData)
        (some (duplicateCfg
          { nextData with
            input := []
            reverse := tokens.reverse ++ nextData.reverse }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def duplicate_evalsInTime (tokens : List WordToken) (data : TapeData)
    (reverseEq : data.reverse = tokens) :
    EvalsToInTime (TM2.step program) (duplicateCfg data)
      (some (scanOuterCfg
        { data with
          reverse := []
          outer := tokens.reverse ++ data.outer
          source := tokens.reverse ++ data.source }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep (step_duplicate_nil data reverseEq)
      convert step using 1 <;> simp
  | cons token tokens induction =>
      let nextData :=
        { data with
          reverse := tokens
          outer := token :: data.outer
          source := token :: data.source }
      have first := oneStep
        (step_duplicate_cons data token tokens reverseEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (duplicateCfg data) (duplicateCfg nextData)
        (some (scanOuterCfg
          { nextData with
            reverse := []
            outer := tokens.reverse ++ nextData.outer
            source := tokens.reverse ++ nextData.source }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
