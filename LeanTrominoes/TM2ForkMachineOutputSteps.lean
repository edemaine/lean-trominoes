/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ForkMachineSetupExecution

/-! # Output-assembly transitions of the fork machine -/

noncomputable section

namespace LeanTrominoes
namespace TM2ForkMachine

open Turing

def outputAssemblyStacks (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (firstOutput : List (first.Γ first.k₁))
    (secondOutput : List (second.Γ second.k₁))
    (outputReverse output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    ∀ stack,
      List (Alphabet first second InputSymbol FirstSymbol SecondSymbol stack)
  | .input => []
  | .inputReverse => []
  | .first stack => (haltList first firstOutput).stk stack
  | .second stack => (haltList second secondOutput).stk stack
  | .outputReverse => outputReverse
  | .output => output

def outputAssemblyCfg (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (label : CombinedLabel first second)
    (state : CombinedState first second InputSymbol FirstSymbol SecondSymbol)
    (firstOutput : List (first.Γ first.k₁))
    (secondOutput : List (second.Γ second.k₁))
    (outputReverse output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    TM2.Cfg
      (Alphabet first second InputSymbol FirstSymbol SecondSymbol)
      (CombinedLabel first second)
      (CombinedState first second InputSymbol FirstSymbol SecondSymbol) where
  l := some label
  var := state
  stk := outputAssemblyStacks first second
    InputSymbol FirstSymbol SecondSymbol
    firstOutput secondOutput outputReverse output

section

variable {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
variable [Fintype InputSymbol] [Fintype FirstSymbol] [Fintype SecondSymbol]
variable [Inhabited InputSymbol] [Inhabited FirstSymbol]
variable [Inhabited SecondSymbol]
variable {encodeInput : Input → List InputSymbol}
variable {encodeFirst : FirstOutput → List FirstSymbol}
variable {encodeSecond : SecondOutput → List SecondSymbol}
variable {firstFunction : Input → FirstOutput}
variable {secondFunction : Input → SecondOutput}
variable (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
variable (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction)

theorem step_drainFirstOutput_cons
    (symbol : first.tm.Γ first.tm.k₁)
    (remaining : List (first.tm.Γ first.tm.k₁))
    (secondOutput : List (second.tm.Γ second.tm.k₁))
    (outputReverse output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    (machine first second).step
        (outputAssemblyCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol .drainFirstOutput
          (.firstOutput none) (symbol :: remaining) secondOutput
          outputReverse output) =
      some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .pushFirstOutput
        (.firstOutput (some (first.outputAlphabet symbol)))
        remaining secondOutput outputReverse output) := by
  simp [FinTM2.step, TM2.step, machine, outputAssemblyCfg,
    outputAssemblyStacks, program, firstOutputSymbol, haltList]
  congr 2
  funext stack
  cases stack with
  | input => simp [outputAssemblyStacks]
  | inputReverse => simp [outputAssemblyStacks]
  | first stack =>
      by_cases equal : stack = first.tm.k₁
      · subst stack
        simp [outputAssemblyStacks, haltList]
      · simp [outputAssemblyStacks, haltList, equal]
  | second stack => simp [outputAssemblyStacks]
  | outputReverse => simp [outputAssemblyStacks]
  | output => simp [outputAssemblyStacks]

theorem step_pushFirstOutput
    (symbol : FirstSymbol)
    (firstOutput : List (first.tm.Γ first.tm.k₁))
    (secondOutput : List (second.tm.Γ second.tm.k₁))
    (outputReverse output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    (machine first second).step
        (outputAssemblyCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol .pushFirstOutput
          (.firstOutput (some symbol)) firstOutput secondOutput
          outputReverse output) =
      some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainFirstOutput
        (.firstOutput none) firstOutput secondOutput
        (.inl symbol :: outputReverse) output) := by
  simp [FinTM2.step, TM2.step, machine, outputAssemblyCfg,
    outputAssemblyStacks, program, firstOutputSymbol]
  congr 2
  funext stack
  cases stack <;> simp [outputAssemblyStacks]

theorem step_drainFirstOutput_nil
    (secondOutput : List (second.tm.Γ second.tm.k₁))
    (outputReverse output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    (machine first second).step
        (outputAssemblyCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol .drainFirstOutput
          (.firstOutput none) [] secondOutput outputReverse output) =
      some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .pushSeparator
        (.firstOutput none) [] secondOutput outputReverse output) := by
  simp [FinTM2.step, TM2.step, machine, outputAssemblyCfg,
    outputAssemblyStacks, program, firstOutputSymbol, haltList]
  congr 2
  funext stack
  cases stack with
  | input => simp [outputAssemblyStacks]
  | inputReverse => simp [outputAssemblyStacks]
  | first stack =>
      by_cases equal : stack = first.tm.k₁
      · subst stack
        simp [outputAssemblyStacks, haltList]
      · simp [outputAssemblyStacks, haltList, equal]
  | second stack => simp [outputAssemblyStacks]
  | outputReverse => simp [outputAssemblyStacks]
  | output => simp [outputAssemblyStacks]

theorem step_pushSeparator
    (secondOutput : List (second.tm.Γ second.tm.k₁))
    (outputReverse output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    (machine first second).step
        (outputAssemblyCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol .pushSeparator
          (.firstOutput none) [] secondOutput outputReverse output) =
      some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainSecondOutput
        (.secondOutput none) [] secondOutput
        (.inr (.inl ()) :: outputReverse) output) := by
  simp [FinTM2.step, TM2.step, machine, outputAssemblyCfg,
    outputAssemblyStacks, program]
  congr 2
  funext stack
  cases stack <;> simp [outputAssemblyStacks]

theorem step_drainSecondOutput_cons
    (symbol : second.tm.Γ second.tm.k₁)
    (remaining : List (second.tm.Γ second.tm.k₁))
    (outputReverse output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    (machine first second).step
        (outputAssemblyCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol .drainSecondOutput
          (.secondOutput none) [] (symbol :: remaining)
          outputReverse output) =
      some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .pushSecondOutput
        (.secondOutput (some (second.outputAlphabet symbol)))
        [] remaining outputReverse output) := by
  simp [FinTM2.step, TM2.step, machine, outputAssemblyCfg,
    outputAssemblyStacks, program, secondOutputSymbol, haltList]
  congr 2
  funext stack
  cases stack with
  | input => simp [outputAssemblyStacks]
  | inputReverse => simp [outputAssemblyStacks]
  | first stack => simp [outputAssemblyStacks]
  | second stack =>
      by_cases equal : stack = second.tm.k₁
      · subst stack
        simp [outputAssemblyStacks, haltList]
      · simp [outputAssemblyStacks, haltList, equal]
  | outputReverse => simp [outputAssemblyStacks]
  | output => simp [outputAssemblyStacks]

theorem step_pushSecondOutput
    (symbol : SecondSymbol)
    (secondOutput : List (second.tm.Γ second.tm.k₁))
    (outputReverse output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    (machine first second).step
        (outputAssemblyCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol .pushSecondOutput
          (.secondOutput (some symbol)) [] secondOutput
          outputReverse output) =
      some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainSecondOutput
        (.secondOutput none) [] secondOutput
        (.inr (.inr symbol) :: outputReverse) output) := by
  simp [FinTM2.step, TM2.step, machine, outputAssemblyCfg,
    outputAssemblyStacks, program, secondOutputSymbol]
  congr 2
  funext stack
  cases stack <;> simp [outputAssemblyStacks]

theorem step_drainSecondOutput_nil
    (outputReverse output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    (machine first second).step
        (outputAssemblyCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol .drainSecondOutput
          (.secondOutput none) [] [] outputReverse output) =
      some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainOutputReverse
        (.output none) [] [] outputReverse output) := by
  simp [FinTM2.step, TM2.step, machine, outputAssemblyCfg,
    outputAssemblyStacks, program, secondOutputSymbol, haltList]
  congr 2
  funext stack
  cases stack with
  | input => simp [outputAssemblyStacks]
  | inputReverse => simp [outputAssemblyStacks]
  | first stack => simp [outputAssemblyStacks]
  | second stack =>
      by_cases equal : stack = second.tm.k₁
      · subst stack
        simp [outputAssemblyStacks, haltList]
      · simp [outputAssemblyStacks, haltList, equal]
  | outputReverse => simp [outputAssemblyStacks]
  | output => simp [outputAssemblyStacks]

theorem step_drainOutputReverse_cons
    (symbol : OutputSymbol FirstSymbol SecondSymbol)
    (remaining output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    (machine first second).step
        (outputAssemblyCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol .drainOutputReverse
          (.output none) [] [] (symbol :: remaining) output) =
      some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .pushOutput
        (.output (some symbol)) [] [] remaining output) := by
  simp [FinTM2.step, TM2.step, machine, outputAssemblyCfg,
    outputAssemblyStacks, program, outputSymbol]
  congr 2
  funext stack
  cases stack <;> simp [outputAssemblyStacks]

theorem step_pushOutput
    (symbol : OutputSymbol FirstSymbol SecondSymbol)
    (remaining output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    (machine first second).step
        (outputAssemblyCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol .pushOutput
          (.output (some symbol)) [] [] remaining output) =
      some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainOutputReverse
        (.output none) [] [] remaining (symbol :: output)) := by
  simp [FinTM2.step, TM2.step, machine, outputAssemblyCfg,
    outputAssemblyStacks, program, outputSymbol]
  congr 2
  funext stack
  cases stack <;> simp [outputAssemblyStacks]

theorem step_drainOutputReverse_nil
    (output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    (machine first second).step
        (outputAssemblyCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol .drainOutputReverse
          (.output none) [] [] [] output) =
      some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .finish
        (.output none) [] [] [] output) := by
  simp [FinTM2.step, TM2.step, machine, outputAssemblyCfg,
    outputAssemblyStacks, program, outputSymbol]
  congr 2
  funext stack
  cases stack <;> simp [outputAssemblyStacks]

theorem step_finish
    (output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    (machine first second).step
        (outputAssemblyCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol .finish
          (.output none) [] [] [] output) =
      some (haltList (machine first second) output) := by
  simp [FinTM2.step, TM2.step, machine, outputAssemblyCfg,
    program, haltList]
  congr 2
  funext stack
  cases stack with
  | input => simp [outputAssemblyStacks]
  | inputReverse => simp [outputAssemblyStacks]
  | first stack =>
      by_cases equal : stack = first.tm.k₁
      · subst stack
        simp [outputAssemblyStacks, haltList]
      · simp [outputAssemblyStacks, haltList, equal]
  | second stack =>
      by_cases equal : stack = second.tm.k₁
      · subst stack
        simp [outputAssemblyStacks, haltList]
      · simp [outputAssemblyStacks, haltList, equal]
  | outputReverse => simp [outputAssemblyStacks]
  | output => simp [outputAssemblyStacks]

end

end TM2ForkMachine
end LeanTrominoes
