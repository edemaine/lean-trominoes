/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryRotatedRanksFieldSteps

/-! # Local execution loops for unary rotated ranks -/

noncomputable section

namespace LeanTrominoes
namespace UnaryRotatedRanksMachine

open StateTransition Turing

private def oneStep {before after : machine.Cfg}
    (step : machine.step before = some after) :
    EvalsToInTime machine.step before (some after) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    exact step
  steps_le_m := Nat.le_refl 1

theorem replicate_unit_cons_comm (count : Nat) (tail : List UnarySymbol) :
    List.replicate count (.unit : UnarySymbol) ++ .unit :: tail =
      .unit :: (List.replicate count (.unit : UnarySymbol) ++ tail) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [List.replicate_succ, List.cons_append,
        List.cons.injEq, true_and]
      exact induction

def copyPositive_evalsInTime (units : Nat)
    (tail : List UnarySymbol) (data : TapeData)
    (ranksEq : data.ranks =
      List.replicate units .unit ++ .delimiter :: tail) :
    EvalsToInTime machine.step (positiveRankRestCfg data)
      (some (drainSizeCfg
        { data with
          ranks := tail
          outputReverse :=
            List.replicate units .unit ++ data.outputReverse }))
      (2 * units + 1) := by
  induction units generalizing data with
  | zero =>
      have step := step_positiveRankRest_delimiter data tail
        (by simpa using ranksEq)
      simpa using oneStep step
  | succ units induction =>
      have ranksHead : data.ranks = .unit ::
          (List.replicate units .unit ++ .delimiter :: tail) := by
        simpa [List.replicate_succ] using ranksEq
      let popped := oneStep
        (step_positiveRankRest_unit data
          (List.replicate units .unit ++ .delimiter :: tail) ranksHead)
      let pushed := oneStep
        (step_pushPositiveUnit
          { data with
            ranks := List.replicate units .unit ++ .delimiter :: tail })
      let nextData : TapeData :=
        { data with
          ranks := List.replicate units .unit ++ .delimiter :: tail
          outputReverse := .unit :: data.outputReverse }
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * units + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.replicate_succ, Nat.mul_add,
        replicate_unit_cons_comm, List.append_assoc,
        Nat.add_assoc] using whole

def copyZero_evalsInTime (units : Nat)
    (tail : List UnarySymbol) (data : TapeData)
    (sizesEq : data.sizes =
      List.replicate units .unit ++ .delimiter :: tail) :
    EvalsToInTime machine.step (zeroRankRestSizeCfg data)
      (some (emitDelimiterCfg
        { data with
          sizes := tail
          outputReverse :=
            List.replicate units .unit ++ data.outputReverse }))
      (2 * units + 1) := by
  induction units generalizing data with
  | zero =>
      have step := step_zeroRankRestSize_delimiter data tail
        (by simpa using sizesEq)
      simpa using oneStep step
  | succ units induction =>
      have sizesHead : data.sizes = .unit ::
          (List.replicate units .unit ++ .delimiter :: tail) := by
        simpa [List.replicate_succ] using sizesEq
      let popped := oneStep
        (step_zeroRankRestSize_unit data
          (List.replicate units .unit ++ .delimiter :: tail) sizesHead)
      let pushed := oneStep
        (step_pushZeroUnit
          { data with
            sizes := List.replicate units .unit ++ .delimiter :: tail })
      let nextData : TapeData :=
        { data with
          sizes := List.replicate units .unit ++ .delimiter :: tail
          outputReverse := .unit :: data.outputReverse }
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * units + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.replicate_succ, Nat.mul_add,
        replicate_unit_cons_comm, List.append_assoc,
        Nat.add_assoc] using whole

def drainSize_evalsInTime (size : Nat) (tail : List UnarySymbol)
    (data : TapeData)
    (sizesEq : data.sizes =
      UnaryFieldEncoderMachine.unaryField size ++ tail) :
    EvalsToInTime machine.step (drainSizeCfg data)
      (some (emitDelimiterCfg { data with sizes := tail }))
      (size + 1) := by
  induction size generalizing data with
  | zero =>
      have step := step_drainSize_delimiter data tail
        (by simpa [UnaryFieldEncoderMachine.unaryField] using sizesEq)
      simpa using oneStep step
  | succ size induction =>
      have sizesHead : data.sizes = .unit ::
          (UnaryFieldEncoderMachine.unaryField size ++ tail) := by
        simpa [UnaryFieldEncoderMachine.unaryField,
          List.replicate_succ] using sizesEq
      let first := oneStep
        (step_drainSize_unit data
          (UnaryFieldEncoderMachine.unaryField size ++ tail) sizesHead)
      let nextData : TapeData :=
        { data with
          sizes := UnaryFieldEncoderMachine.unaryField size ++ tail }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        1 (size + 1) _ _ _ first rest
      simpa [whole, nextData, Nat.add_assoc] using whole

def reverseOutput_evalsInTime (tokens : List UnarySymbol)
    (data : TapeData) (reverseEq : data.outputReverse = tokens) :
    EvalsToInTime machine.step (reverseOutputCfg data)
      (some (haltDataCfg
        { data with
          outputReverse := []
          output := tokens.reverse ++ data.output }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_reverseOutput_nil data reverseEq
      simpa using oneStep step
  | cons symbol tokens induction =>
      let popped := oneStep
        (step_reverseOutput_cons data symbol tokens reverseEq)
      let pushed := oneStep
        (step_pushOutput { data with outputReverse := tokens } symbol)
      let nextData : TapeData :=
        { data with
          outputReverse := tokens
          output := symbol :: data.output }
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end UnaryRotatedRanksMachine
end LeanTrominoes
