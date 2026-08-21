/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupOutputSteps

/-! # Local loops of last-true unary lookup -/

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

theorem replicate_unit_cons_comm (count : Nat) (tail : List UnarySymbol) :
    List.replicate count (.unit : UnarySymbol) ++ .unit :: tail =
      .unit :: (List.replicate count (.unit : UnarySymbol) ++ tail) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [List.replicate_succ, List.cons_append,
        List.cons.injEq, true_and]
      exact induction

def clearCandidate_evalsInTime (selected : Bool) (candidate : List Unit)
    (data : TapeData) (candidateEq : data.candidate = candidate) :
    EvalsToInTime machine.step (clearCandidateCfg selected data)
      (some (readValueCfg selected { data with candidate := [] }))
      (candidate.length + 1) := by
  induction candidate generalizing data with
  | nil =>
      have step := step_clearCandidate_nil data selected candidateEq
      simpa using oneStep step
  | cons unitValue candidate induction =>
      rcases unitValue with ⟨⟩
      let first := oneStep
        (step_clearCandidate_cons data selected candidate candidateEq)
      let nextData : TapeData := { data with candidate := candidate }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        1 (candidate.length + 1) _ _ _ first rest
      simpa [whole, nextData, Nat.add_assoc] using whole

def drainCandidate_evalsInTime (candidate : List Unit) (data : TapeData)
    (candidateEq : data.candidate = candidate) :
    EvalsToInTime machine.step (drainCandidateCfg data)
      (some (emitDelimiterCfg
        { data with
          candidate := []
          outputReverse :=
            List.replicate candidate.length .unit ++ data.outputReverse }))
      (2 * candidate.length + 1) := by
  induction candidate generalizing data with
  | nil =>
      have step := step_drainCandidate_nil data candidateEq
      simpa using oneStep step
  | cons unitValue candidate induction =>
      rcases unitValue with ⟨⟩
      let popped := oneStep
        (step_drainCandidate_cons data candidate candidateEq)
      let pushed := oneStep
        (step_pushOutputUnit { data with candidate := candidate })
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let nextData : TapeData :=
        { data with
          candidate := candidate
          outputReverse := .unit :: data.outputReverse }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        2 (2 * candidate.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.replicate_succ, Nat.mul_add,
        replicate_unit_cons_comm, List.append_assoc,
        Nat.add_assoc] using whole

def restoreValues_evalsInTime (tokens : List UnarySymbol)
    (data : TapeData) (restoreEq : data.valuesRestore = tokens) :
    EvalsToInTime machine.step (restoreValuesCfg data)
      (some (scanRowsCfg
        { data with
          valuesRestore := []
          values := tokens.reverse ++ data.values }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_restoreValues_nil data restoreEq
      simpa using oneStep step
  | cons symbol tokens induction =>
      let popped := oneStep
        (step_restoreValues_cons data symbol tokens restoreEq)
      let pushed := oneStep
        (step_pushRestoredValue
          { data with valuesRestore := tokens } symbol)
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let nextData : TapeData :=
        { data with
          valuesRestore := tokens
          values := symbol :: data.values }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

def clearValues_evalsInTime (tokens : List UnarySymbol)
    (data : TapeData) (valuesEq : data.values = tokens) :
    EvalsToInTime machine.step (clearValuesCfg data)
      (some (reverseOutputCfg { data with values := [] }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_clearValues_nil data valuesEq
      simpa using oneStep step
  | cons symbol tokens induction =>
      let first := oneStep
        (step_clearValues_cons data symbol tokens valuesEq)
      let nextData : TapeData := { data with values := tokens }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        1 (tokens.length + 1) _ _ _ first rest
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
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let nextData : TapeData :=
        { data with
          outputReverse := tokens
          output := symbol :: data.output }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
