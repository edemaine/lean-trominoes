/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ForkMachineSetupSteps

/-! # Complete input duplication for the fork machine -/

noncomputable section

namespace LeanTrominoes
namespace TM2ForkMachine

open StateTransition Turing

private def evalsToInTime_single
    {Configuration : Type} {transition : Configuration → Option Configuration}
    {before after : Configuration} (step : transition before = some after) :
    EvalsToInTime transition before (some after) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    exact step
  steps_le_m := Nat.le_refl 1

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

/-- The first setup pass reverses the semantic input onto the dedicated
reverse stack. -/
def drainInputRun
    (input inputReverse : List InputSymbol)
    (firstInput : List (first.tm.Γ first.tm.k₀))
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    EvalsToInTime (machine first second).step
      (setupCfg first.tm second.tm InputSymbol FirstSymbol SecondSymbol
        .drainInput (.setup none) input inputReverse
        firstInput secondInput)
      (some (setupCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainInputReverse
        (.setup none) [] (input.reverse ++ inputReverse)
        firstInput secondInput))
      (2 * input.length + 1) := by
  induction input generalizing inputReverse with
  | nil =>
      refine
        { steps := 1
          evals_in_steps := ?_
          steps_le_m := by simp }
      simp only [Function.iterate_one]
      change (machine first second).step
        (setupCfg first.tm second.tm InputSymbol FirstSymbol SecondSymbol
          .drainInput (.setup none) [] inputReverse
          firstInput secondInput) = _
      exact step_drainInput_nil first second
        inputReverse firstInput secondInput
  | cons symbol remaining induction =>
      let popped := evalsToInTime_single
        (step_drainInput_cons first second symbol remaining inputReverse
          firstInput secondInput)
      let pushed := evalsToInTime_single
        (step_pushInputReverse first second symbol remaining inputReverse
          firstInput secondInput)
      let firstTwo := EvalsToInTime.trans (machine first second).step
        1 1 _ _ _ popped pushed
      let rest := induction (symbol :: inputReverse)
      let whole := EvalsToInTime.trans (machine first second).step
        2 (2 * remaining.length + 1) _ _ _ firstTwo rest
      simpa [whole, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

/-- The second setup pass restores the input order onto both component input
stacks. -/
def distributeInputRun
    (inputReverse : List InputSymbol)
    (firstInput : List (first.tm.Γ first.tm.k₀))
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    EvalsToInTime (machine first second).step
      (setupCfg first.tm second.tm InputSymbol FirstSymbol SecondSymbol
        .drainInputReverse (.setup none) [] inputReverse
        firstInput secondInput)
      (some (liftFirstCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol
        (initList second.tm
          ((inputReverse.map second.inputAlphabet.invFun).reverse ++
            secondInput)).stk
        (initList first.tm
          ((inputReverse.map first.inputAlphabet.invFun).reverse ++
            firstInput))))
      (3 * inputReverse.length + 1) := by
  induction inputReverse generalizing firstInput secondInput with
  | nil =>
      refine
        { steps := 1
          evals_in_steps := ?_
          steps_le_m := by simp }
      simp only [Function.iterate_one]
      change (machine first second).step
        (setupCfg first.tm second.tm InputSymbol FirstSymbol SecondSymbol
          .drainInputReverse (.setup none) [] []
          firstInput secondInput) = _
      exact step_drainInputReverse_nil first second
        firstInput secondInput
  | cons symbol remaining induction =>
      let popped := evalsToInTime_single
        (step_drainInputReverse_cons first second symbol remaining
          firstInput secondInput)
      let pushedFirst := evalsToInTime_single
        (step_pushFirstInput first second symbol remaining
          firstInput secondInput)
      let firstTwo := EvalsToInTime.trans (machine first second).step
        1 1 _ _ _ popped pushedFirst
      let pushedSecond := evalsToInTime_single
        (step_pushSecondInput first second symbol remaining
          (first.inputAlphabet.invFun symbol :: firstInput) secondInput)
      let firstThree := EvalsToInTime.trans (machine first second).step
        2 1 _ _ _ firstTwo pushedSecond
      let rest := induction
        (first.inputAlphabet.invFun symbol :: firstInput)
        (second.inputAlphabet.invFun symbol :: secondInput)
      let whole := EvalsToInTime.trans (machine first second).step
        3 (3 * remaining.length + 1) _ _ _ firstThree rest
      simpa [whole, List.reverse_cons, Nat.mul_add, List.map_cons,
        List.append_assoc, Nat.add_assoc] using whole

theorem initList_machine_eq_setup (input : List InputSymbol) :
    initList (machine first second) input =
      setupCfg first.tm second.tm InputSymbol FirstSymbol SecondSymbol
        .drainInput (.setup none) input [] [] [] := by
  simp only [initList, machine, setupCfg]
  congr 1
  funext stack
  cases stack with
  | input => simp [setupStacks]
  | inputReverse => simp [setupStacks]
  | first stack =>
      by_cases equal : stack = first.tm.k₀
      · subst stack
        simp [setupStacks, initList]
      · simp [setupStacks, initList, equal]
  | second stack =>
      by_cases equal : stack = second.tm.k₀
      · subst stack
        simp [setupStacks, initList]
      · simp [setupStacks, initList, equal]
  | outputReverse => simp [setupStacks]
  | output => simp [setupStacks]

/-- Starting from the fork machine's native input layout, setup prepares the
two child inputs in semantic order and enters the first component. -/
def setupRun (input : List InputSymbol) :
    EvalsToInTime (machine first second).step
      (initList (machine first second) input)
      (some (liftFirstCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol
        (initList second.tm
          (input.map second.inputAlphabet.invFun)).stk
        (initList first.tm
          (input.map first.inputAlphabet.invFun))))
      (5 * input.length + 2) := by
  have firstPass := drainInputRun first second input [] [] []
  have secondPass := distributeInputRun first second input.reverse [] []
  have firstPass' : EvalsToInTime (machine first second).step
      (setupCfg first.tm second.tm InputSymbol FirstSymbol SecondSymbol
        .drainInput (.setup none) input [] [] [])
      (some (setupCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainInputReverse
        (.setup none) [] input.reverse [] []))
      (2 * input.length + 1) := by
    simpa using firstPass
  let whole := EvalsToInTime.trans (machine first second).step
    (2 * input.length + 1) (3 * input.reverse.length + 1)
    _ _ _ firstPass' secondPass
  simp only [List.length_reverse] at whole
  rw [initList_machine_eq_setup first second input]
  convert whole using 1
  · simp [List.map_reverse]
  · omega

end

end TM2ForkMachine
end LeanTrominoes
