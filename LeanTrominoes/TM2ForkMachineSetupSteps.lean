/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ForkMachineComponentExecution

/-! # Setup transitions of the fork machine -/

noncomputable section

namespace LeanTrominoes
namespace TM2ForkMachine

open Turing

def setupStacks (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (input inputReverse : List InputSymbol)
    (firstInput : List (first.Γ first.k₀))
    (secondInput : List (second.Γ second.k₀)) :
    ∀ stack,
      List (Alphabet first second InputSymbol FirstSymbol SecondSymbol stack)
  | .input => input
  | .inputReverse => inputReverse
  | .first stack => (initList first firstInput).stk stack
  | .second stack => (initList second secondInput).stk stack
  | .outputReverse => []
  | .output => []

def setupCfg (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (label : CombinedLabel first second)
    (state : CombinedState first second InputSymbol FirstSymbol SecondSymbol)
    (input inputReverse : List InputSymbol)
    (firstInput : List (first.Γ first.k₀))
    (secondInput : List (second.Γ second.k₀)) :
    TM2.Cfg
      (Alphabet first second InputSymbol FirstSymbol SecondSymbol)
      (CombinedLabel first second)
      (CombinedState first second InputSymbol FirstSymbol SecondSymbol) where
  l := some label
  var := state
  stk := setupStacks first second InputSymbol FirstSymbol SecondSymbol
    input inputReverse firstInput secondInput

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

theorem step_drainInput_cons
    (symbol : InputSymbol) (remaining inputReverse : List InputSymbol)
    (firstInput : List (first.tm.Γ first.tm.k₀))
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    (machine first second).step
        (setupCfg first.tm second.tm InputSymbol FirstSymbol SecondSymbol
          .drainInput (.setup none) (symbol :: remaining) inputReverse
          firstInput secondInput) =
      some (setupCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .pushInputReverse
        (.setup (some symbol)) remaining inputReverse
        firstInput secondInput) := by
  simp [FinTM2.step, TM2.step, machine, setupCfg, setupStacks,
    program, setupSymbol]
  congr 2
  funext stack
  cases stack <;> simp [setupStacks]

theorem step_pushInputReverse
    (symbol : InputSymbol) (remaining inputReverse : List InputSymbol)
    (firstInput : List (first.tm.Γ first.tm.k₀))
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    (machine first second).step
        (setupCfg first.tm second.tm InputSymbol FirstSymbol SecondSymbol
          .pushInputReverse (.setup (some symbol)) remaining inputReverse
          firstInput secondInput) =
      some (setupCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainInput (.setup none)
        remaining (symbol :: inputReverse) firstInput secondInput) := by
  simp [FinTM2.step, TM2.step, machine, setupCfg, setupStacks,
    program, setupSymbol]
  congr 2
  funext stack
  cases stack <;> simp [setupStacks]

theorem step_drainInput_nil
    (inputReverse : List InputSymbol)
    (firstInput : List (first.tm.Γ first.tm.k₀))
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    (machine first second).step
        (setupCfg first.tm second.tm InputSymbol FirstSymbol SecondSymbol
          .drainInput (.setup none) [] inputReverse
          firstInput secondInput) =
      some (setupCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainInputReverse
        (.setup none) [] inputReverse firstInput secondInput) := by
  simp [FinTM2.step, TM2.step, machine, setupCfg, setupStacks,
    program, setupSymbol]
  congr 2
  funext stack
  cases stack <;> simp [setupStacks]

theorem step_drainInputReverse_cons
    (symbol : InputSymbol) (remaining : List InputSymbol)
    (firstInput : List (first.tm.Γ first.tm.k₀))
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    (machine first second).step
        (setupCfg first.tm second.tm InputSymbol FirstSymbol SecondSymbol
          .drainInputReverse (.setup none) [] (symbol :: remaining)
          firstInput secondInput) =
      some (setupCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .pushFirstInput
        (.setup (some symbol)) [] remaining firstInput secondInput) := by
  simp [FinTM2.step, TM2.step, machine, setupCfg, setupStacks,
    program, setupSymbol]
  congr 2
  funext stack
  cases stack <;> simp [setupStacks]

theorem step_pushFirstInput
    (symbol : InputSymbol) (remaining : List InputSymbol)
    (firstInput : List (first.tm.Γ first.tm.k₀))
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    (machine first second).step
        (setupCfg first.tm second.tm InputSymbol FirstSymbol SecondSymbol
          .pushFirstInput (.setup (some symbol)) [] remaining
          firstInput secondInput) =
      some (setupCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .pushSecondInput
        (.setup (some symbol)) [] remaining
        (first.inputAlphabet.invFun symbol :: firstInput) secondInput) := by
  simp [FinTM2.step, TM2.step, machine, setupCfg, setupStacks,
    program, setupSymbol]
  congr 2
  funext stack
  cases stack with
  | input => simp [setupStacks]
  | inputReverse => simp [setupStacks]
  | first stack =>
      by_cases equal : stack = first.tm.k₀
      · subst stack
        simp [setupStacks, initList]
      · simp [setupStacks, initList, equal]
  | second stack => simp [setupStacks]
  | outputReverse => simp [setupStacks]
  | output => simp [setupStacks]

theorem step_pushSecondInput
    (symbol : InputSymbol) (remaining : List InputSymbol)
    (firstInput : List (first.tm.Γ first.tm.k₀))
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    (machine first second).step
        (setupCfg first.tm second.tm InputSymbol FirstSymbol SecondSymbol
          .pushSecondInput (.setup (some symbol)) [] remaining
          firstInput secondInput) =
      some (setupCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainInputReverse
        (.setup none) [] remaining firstInput
        (second.inputAlphabet.invFun symbol :: secondInput)) := by
  simp [FinTM2.step, TM2.step, machine, setupCfg, setupStacks,
    program, setupSymbol]
  congr 2
  funext stack
  cases stack with
  | input => simp [setupStacks]
  | inputReverse => simp [setupStacks]
  | first stack => simp [setupStacks]
  | second stack =>
      by_cases equal : stack = second.tm.k₀
      · subst stack
        simp [setupStacks, initList]
      · simp [setupStacks, initList, equal]
  | outputReverse => simp [setupStacks]
  | output => simp [setupStacks]

theorem step_drainInputReverse_nil
    (firstInput : List (first.tm.Γ first.tm.k₀))
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    (machine first second).step
        (setupCfg first.tm second.tm InputSymbol FirstSymbol SecondSymbol
          .drainInputReverse (.setup none) [] [] firstInput secondInput) =
      some (liftFirstCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol
        (initList second.tm secondInput).stk
        (initList first.tm firstInput)) := by
  simp [FinTM2.step, TM2.step, machine, setupCfg, setupStacks,
    program, setupSymbol, liftFirstCfg]
  congr 2
  funext stack
  cases stack <;> simp [setupStacks, componentStacks]

end

end TM2ForkMachine
end LeanTrominoes
