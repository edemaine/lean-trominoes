/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ForkMachineOutputSteps

/-! # Collecting the two fork outputs around a separator -/

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

def drainFirstOutputRun
    (firstOutput : List (first.tm.Γ first.tm.k₁))
    (secondOutput : List (second.tm.Γ second.tm.k₁))
    (outputReverse output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    EvalsToInTime (machine first second).step
      (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainFirstOutput
        (.firstOutput none) firstOutput secondOutput outputReverse output)
      (some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .pushSeparator
        (.firstOutput none) [] secondOutput
        ((firstOutput.map fun symbol =>
          Sum.inl (first.outputAlphabet symbol)).reverse ++ outputReverse)
        output))
      (2 * firstOutput.length + 1) := by
  induction firstOutput generalizing outputReverse with
  | nil =>
      refine
        { steps := 1
          evals_in_steps := ?_
          steps_le_m := by simp }
      simp only [Function.iterate_one]
      change (machine first second).step
        (outputAssemblyCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol .drainFirstOutput
          (.firstOutput none) [] secondOutput outputReverse output) = _
      exact step_drainFirstOutput_nil first second
        secondOutput outputReverse output
  | cons symbol remaining induction =>
      let popped := evalsToInTime_single
        (step_drainFirstOutput_cons first second symbol remaining
          secondOutput outputReverse output)
      let pushed := evalsToInTime_single
        (step_pushFirstOutput first second (first.outputAlphabet symbol)
          remaining secondOutput outputReverse output)
      let firstTwo := EvalsToInTime.trans (machine first second).step
        1 1 _ _ _ popped pushed
      let rest := induction
        (.inl (first.outputAlphabet symbol) :: outputReverse)
      let whole := EvalsToInTime.trans (machine first second).step
        2 (2 * remaining.length + 1) _ _ _ firstTwo rest
      simpa [whole, List.reverse_cons, List.map_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

def drainSecondOutputRun
    (secondOutput : List (second.tm.Γ second.tm.k₁))
    (outputReverse output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    EvalsToInTime (machine first second).step
      (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainSecondOutput
        (.secondOutput none) [] secondOutput outputReverse output)
      (some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainOutputReverse
        (.output none) [] []
        ((secondOutput.map fun symbol =>
          Sum.inr (Sum.inr (second.outputAlphabet symbol))).reverse ++
            outputReverse)
        output))
      (2 * secondOutput.length + 1) := by
  induction secondOutput generalizing outputReverse with
  | nil =>
      refine
        { steps := 1
          evals_in_steps := ?_
          steps_le_m := by simp }
      simp only [Function.iterate_one]
      change (machine first second).step
        (outputAssemblyCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol .drainSecondOutput
          (.secondOutput none) [] [] outputReverse output) = _
      exact step_drainSecondOutput_nil first second outputReverse output
  | cons symbol remaining induction =>
      let popped := evalsToInTime_single
        (step_drainSecondOutput_cons first second symbol remaining
          outputReverse output)
      let pushed := evalsToInTime_single
        (step_pushSecondOutput first second (second.outputAlphabet symbol)
          remaining outputReverse output)
      let firstTwo := EvalsToInTime.trans (machine first second).step
        1 1 _ _ _ popped pushed
      let rest := induction
        (.inr (.inr (second.outputAlphabet symbol)) :: outputReverse)
      let whole := EvalsToInTime.trans (machine first second).step
        2 (2 * remaining.length + 1) _ _ _ firstTwo rest
      simpa [whole, List.reverse_cons, List.map_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

def collectOutputsRun
    (firstOutput : List (first.tm.Γ first.tm.k₁))
    (secondOutput : List (second.tm.Γ second.tm.k₁)) :
    EvalsToInTime (machine first second).step
      (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainFirstOutput
        (.firstOutput none) firstOutput secondOutput [] [])
      (some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainOutputReverse
        (.output none) [] []
          (((firstOutput.map fun symbol =>
            Sum.inl (first.outputAlphabet symbol)) ++
          [Sum.inr (Sum.inl ())] ++
          (secondOutput.map fun symbol =>
            Sum.inr (Sum.inr (second.outputAlphabet symbol)))).reverse)
        []))
      (2 * firstOutput.length + 2 * secondOutput.length + 3) := by
  have firstRun := drainFirstOutputRun first second
    firstOutput secondOutput [] []
  have separatorRun := evalsToInTime_single
    (step_pushSeparator first second secondOutput
      ((firstOutput.map fun symbol =>
        Sum.inl (first.outputAlphabet symbol)).reverse) [])
  have secondRun := drainSecondOutputRun first second secondOutput
    (.inr (.inl ()) ::
      (firstOutput.map fun symbol =>
        Sum.inl (first.outputAlphabet symbol)).reverse) []
  have firstRun' : EvalsToInTime (machine first second).step
      (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainFirstOutput
        (.firstOutput none) firstOutput secondOutput [] [])
      (some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .pushSeparator
        (.firstOutput none) [] secondOutput
        (firstOutput.map fun symbol =>
          Sum.inl (first.outputAlphabet symbol)).reverse []))
      (2 * firstOutput.length + 1) := by
    simpa using firstRun
  let firstTwo := EvalsToInTime.trans (machine first second).step
    (2 * firstOutput.length + 1) 1 _ _ _ firstRun' separatorRun
  have firstTwo' : EvalsToInTime (machine first second).step
      (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainFirstOutput
        (.firstOutput none) firstOutput secondOutput [] [])
      (some (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainSecondOutput
        (.secondOutput none) [] secondOutput
        (Sum.inr (Sum.inl ()) ::
          (firstOutput.map fun symbol =>
            Sum.inl (first.outputAlphabet symbol)).reverse) []))
      (2 * firstOutput.length + 2) := by
    have timeEq :
        1 + (2 * firstOutput.length + 1) =
          2 * firstOutput.length + 2 := by
      omega
    rw [timeEq] at firstTwo
    exact firstTwo
  let whole := EvalsToInTime.trans (machine first second).step
    (2 * firstOutput.length + 2) (2 * secondOutput.length + 1)
    _ _ _ firstTwo' secondRun
  convert whole using 1
  · simp [List.reverse_append, List.append_assoc]
  · omega

end

end TM2ForkMachine
end LeanTrominoes
