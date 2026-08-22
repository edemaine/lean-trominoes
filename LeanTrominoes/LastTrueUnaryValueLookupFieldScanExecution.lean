/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupLocalExecution

/-! # Scanning one unary value field for last-true lookup -/

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

def rejectedUnits_evalsInTime (units : Nat)
    (tail : List UnarySymbol) (data : TapeData)
    (valuesEq : data.values =
      List.replicate units .unit ++ .delimiter :: tail) :
    EvalsToInTime machine.step (readValueCfg false data)
      (some (nextBitCfg
        { data with
          values := tail
          valuesRestore :=
            (UnaryFieldEncoderMachine.unaryField units).reverse ++
              data.valuesRestore }))
      (2 * units + 2) := by
  induction units generalizing data with
  | zero =>
      have read := oneStep
        (step_readValue_cons data false .delimiter tail (by simpa using valuesEq))
      have pushed := oneStep
        (step_pushValueRestore_delimiter
          { data with values := tail } false)
      have whole := EvalsToInTime.trans machine.step
        1 1 _ _ _ read pushed
      simpa [UnaryFieldEncoderMachine.unaryField] using whole
  | succ units induction =>
      rw [List.replicate_succ, List.cons_append] at valuesEq
      let remaining :=
        List.replicate units (.unit : UnarySymbol) ++ .delimiter :: tail
      have read := oneStep
        (step_readValue_cons data false .unit remaining valuesEq)
      have pushed := oneStep
        (step_pushValueRestore_unit_false
          { data with values := remaining })
      let nextData : TapeData :=
        { data with
          values := remaining
          valuesRestore := .unit :: data.valuesRestore }
      have rest := induction nextData rfl
      have firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ read pushed
      have whole := EvalsToInTime.trans machine.step
        2 (2 * units + 2) _ _ _ firstTwo rest
      simpa [remaining, nextData, UnaryFieldEncoderMachine.unaryField,
        List.replicate_succ, List.reverse_append,
        replicate_unit_cons_comm, List.append_assoc, Nat.mul_add,
        Nat.add_assoc] using whole

def selectedUnits_evalsInTime (units : Nat)
    (tail : List UnarySymbol) (data : TapeData)
    (valuesEq : data.values =
      List.replicate units .unit ++ .delimiter :: tail) :
    EvalsToInTime machine.step (readValueCfg true data)
      (some (nextBitCfg
        { data with
          values := tail
          valuesRestore :=
            (UnaryFieldEncoderMachine.unaryField units).reverse ++
              data.valuesRestore
          candidate := List.replicate units () ++ data.candidate }))
      (3 * units + 2) := by
  induction units generalizing data with
  | zero =>
      have read := oneStep
        (step_readValue_cons data true .delimiter tail (by simpa using valuesEq))
      have pushed := oneStep
        (step_pushValueRestore_delimiter
          { data with values := tail } true)
      have whole := EvalsToInTime.trans machine.step
        1 1 _ _ _ read pushed
      simpa [UnaryFieldEncoderMachine.unaryField] using whole
  | succ units induction =>
      rw [List.replicate_succ, List.cons_append] at valuesEq
      let remaining :=
        List.replicate units (.unit : UnarySymbol) ++ .delimiter :: tail
      have read := oneStep
        (step_readValue_cons data true .unit remaining valuesEq)
      have restored := oneStep
        (step_pushValueRestore_unit_true
          { data with values := remaining })
      have selected := oneStep
        (step_pushCandidateUnit
          { data with
            values := remaining
            valuesRestore := .unit :: data.valuesRestore })
      let nextData : TapeData :=
        { data with
          values := remaining
          valuesRestore := .unit :: data.valuesRestore
          candidate := () :: data.candidate }
      have rest := induction nextData rfl
      have firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ read restored
      have firstThree := EvalsToInTime.trans machine.step
        2 1 _ _ _ firstTwo selected
      have whole := EvalsToInTime.trans machine.step
        3 (3 * units + 2) _ _ _ firstThree rest
      simpa [remaining, nextData, UnaryFieldEncoderMachine.unaryField,
        List.replicate_succ, List.reverse_append,
        replicate_unit_cons_comm, replicate_candidate_cons_comm,
        List.append_assoc, Nat.mul_add,
        Nat.add_assoc] using whole

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
