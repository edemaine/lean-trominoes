/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerData

/-! # Exact execution of finite-state word transducers -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace FiniteStateTransducer

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    change (some first).bind transition = some last
    simpa using step
  steps_le_m := Nat.le_refl 1

/-- The input phase reaches the terminal-emission label with the semantic
scan output stored in reverse order. -/
def scan_evalsInTime {Control Source Target : Type}
    [Fintype Control] [Fintype Source] [Fintype Target] [Inhabited Target]
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (control : Control)
    (input : List Source) (accumulator : List Target) :
    let scanned := scan transition control input
    EvalsToInTime (TM2.step (program transition finish))
      (scanCfg control input accumulator)
      (some (finishCfg scanned.1
        (scanned.2.reverse ++ accumulator)))
      (2 * input.length + 1) := by
  induction input generalizing control accumulator with
  | nil =>
      simpa [scan] using
        oneStep (step_scan_nil transition finish control accumulator)
  | cons symbol input induction =>
      let current := transition control symbol
      let emitted := current.2.reverse ++ accumulator
      have popStep : EvalsToInTime (TM2.step (program transition finish))
          (scanCfg control (symbol :: input) accumulator)
          (some (emitCfg control symbol input accumulator)) 1 :=
        oneStep (step_scan_cons transition finish control symbol
          input accumulator)
      have emitStep : EvalsToInTime (TM2.step (program transition finish))
          (emitCfg control symbol input accumulator)
          (some (scanCfg current.1 input emitted)) 1 := by
        simpa [current, emitted] using
          oneStep (step_emit transition finish control symbol
            input accumulator)
      have first := EvalsToInTime.trans _ 1 1 _ _ _ popStep emitStep
      have rest := induction current.1 emitted
      have composed := EvalsToInTime.trans _ 2
        (2 * input.length + 1) _ _ _ first rest
      simpa [scan, current, emitted, List.reverse_append,
        List.append_assoc, Nat.mul_add] using composed

/-- Terminal output is prepended to the reverse accumulator in one step. -/
def finish_evalsInTime {Control Source Target : Type}
    [Fintype Control] [Fintype Source] [Fintype Target] [Inhabited Target]
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (control : Control)
    (accumulator : List Target) :
    EvalsToInTime (TM2.step (program transition finish))
      (finishCfg control accumulator)
      (some (reverseCfg ((finish control).reverse ++ accumulator) [])) 1 :=
  oneStep (step_finish transition finish control accumulator)

/-- Reversal moves the complete accumulated word to the output stack. -/
def reverse_evalsInTime {Control Source Target : Type}
    [Fintype Control] [Fintype Source] [Fintype Target] [Inhabited Target]
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target)
    (accumulator output : List Target) :
    EvalsToInTime (TM2.step (program transition finish))
      (reverseCfg accumulator output)
      (some (haltCfg (accumulator.reverse ++ output)))
      (accumulator.length + 1) := by
  induction accumulator generalizing output with
  | nil =>
      simpa using oneStep (step_reverse_nil transition finish output)
  | cons symbol accumulator induction =>
      have first : EvalsToInTime (TM2.step (program transition finish))
          (reverseCfg (symbol :: accumulator) output)
          (some (reverseCfg accumulator (symbol :: output))) 1 :=
        oneStep (step_reverse_cons transition finish symbol
          accumulator output)
      have rest := induction (symbol :: output)
      have composed := EvalsToInTime.trans _ 1
        (accumulator.length + 1) _ _ _ first rest
      simpa [List.reverse_cons, List.append_assoc] using composed

theorem initList_eq_scanCfg {Control Source Target : Type}
    [Fintype Control] [Fintype Source] [Fintype Target] [Inhabited Target]
    (initial : Control)
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (input : List Source) :
    initList (machine Control Source Target initial transition finish) input =
      scanCfg initial input [] := by
  apply congrArg (fun stackValues =>
    TM2.Cfg.mk (some (Label.scan initial)) none stackValues)
  funext stack
  cases stack <;> simp [machine, tapes]

theorem haltList_eq_haltCfg {Control Source Target : Type}
    [Fintype Control] [Fintype Source] [Fintype Target] [Inhabited Target]
    (initial : Control)
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (output : List Target) :
    haltList (machine Control Source Target initial transition finish) output =
      haltCfg output := by
  apply congrArg (fun stackValues =>
    TM2.Cfg.mk none none stackValues)
  funext stack
  cases stack <;> simp [machine, tapes]

/-- Exact complete execution time of the stateful transducer. -/
def outputsInExactTime {Control Source Target : Type}
    [Fintype Control] [Fintype Source] [Fintype Target] [Inhabited Target]
    (initial : Control)
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (input : List Source) :
    TM2OutputsInTime
      (machine Control Source Target initial transition finish) input
      (some (output initial transition finish input))
      (2 * input.length +
        (output initial transition finish input).length + 3) := by
  let scanned := scan transition initial input
  have scannedRun := scan_evalsInTime transition finish initial input []
  have finishedRun := finish_evalsInTime transition finish
    scanned.1 scanned.2.reverse
  have first := EvalsToInTime.trans _
    (2 * input.length + 1) 1 _ _ _ (by
      simpa [scanned] using scannedRun) finishedRun
  have reversedRun := reverse_evalsInTime transition finish
    ((finish scanned.1).reverse ++ scanned.2.reverse) []
  have accumulatorEq :
      (finish scanned.1).reverse ++ scanned.2.reverse =
        (output initial transition finish input).reverse := by
    simp [output, scanned, List.reverse_append]
  rw [accumulatorEq] at first reversedRun
  have first' : EvalsToInTime (TM2.step (program transition finish))
      (scanCfg initial input [])
      (some (reverseCfg
        (output initial transition finish input).reverse []))
      (2 * input.length + 2) := by
    convert first using 1
    omega
  have composed := EvalsToInTime.trans _
    (2 * input.length + 2)
    ((output initial transition finish input).length + 1)
    _ _ _ first' (by simpa using reversedRun)
  change EvalsToInTime
    (TM2.step (program transition finish))
    (initList (machine Control Source Target initial transition finish) input)
    (some (haltList
      (machine Control Source Target initial transition finish)
      (output initial transition finish input)))
    (2 * input.length +
      (output initial transition finish input).length + 3)
  rw [initList_eq_scanCfg initial transition finish input,
    haltList_eq_haltCfg initial transition finish]
  exact
    { toEvalsTo := composed.toEvalsTo
      steps_le_m := composed.steps_le_m.trans (by omega) }

end FiniteStateTransducer
end LeanTrominoes
