/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ForkMachineOutputCollection

/-! # Complete output assembly for the fork machine -/

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

def physicalSeparated
    (firstOutput : List (first.tm.Γ first.tm.k₁))
    (secondOutput : List (second.tm.Γ second.tm.k₁)) :
    List (OutputSymbol FirstSymbol SecondSymbol) :=
  (firstOutput.map fun symbol => Sum.inl (first.outputAlphabet symbol)) ++
    [Sum.inr (Sum.inl ())] ++
    (secondOutput.map fun symbol =>
      Sum.inr (Sum.inr (second.outputAlphabet symbol)))

/-- Reverse the accumulated physical word onto the designated output stack
and enter the canonical halt configuration. -/
def reverseOutputRun
    (outputReverse output : List (OutputSymbol FirstSymbol SecondSymbol)) :
    EvalsToInTime (machine first second).step
      (outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainOutputReverse
        (.output none) [] [] outputReverse output)
      (some (haltList (machine first second)
        (outputReverse.reverse ++ output)))
      (2 * outputReverse.length + 2) := by
  induction outputReverse generalizing output with
  | nil =>
      have drained : EvalsToInTime (machine first second).step
          (outputAssemblyCfg first.tm second.tm
            InputSymbol FirstSymbol SecondSymbol .drainOutputReverse
            (.output none) [] [] [] output)
          (some (outputAssemblyCfg first.tm second.tm
            InputSymbol FirstSymbol SecondSymbol .finish
            (.output none) [] [] [] output)) 1 := by
        refine
          { steps := 1
            evals_in_steps := ?_
            steps_le_m := by simp }
        simp only [Function.iterate_one]
        change (machine first second).step
          (outputAssemblyCfg first.tm second.tm
            InputSymbol FirstSymbol SecondSymbol .drainOutputReverse
            (.output none) [] [] [] output) = _
        exact step_drainOutputReverse_nil first second output
      have finished : EvalsToInTime (machine first second).step
          (outputAssemblyCfg first.tm second.tm
            InputSymbol FirstSymbol SecondSymbol .finish
            (.output none) [] [] [] output)
          (some (haltList (machine first second) output)) 1 := by
        refine
          { steps := 1
            evals_in_steps := ?_
            steps_le_m := by simp }
        simp only [Function.iterate_one]
        change (machine first second).step
          (outputAssemblyCfg first.tm second.tm
            InputSymbol FirstSymbol SecondSymbol .finish
            (.output none) [] [] [] output) = _
        exact step_finish first second output
      let whole := EvalsToInTime.trans (machine first second).step
        1 1 _ _ _ drained finished
      simpa [whole] using whole
  | cons symbol remaining induction =>
      let popped := evalsToInTime_single
        (step_drainOutputReverse_cons first second symbol remaining output)
      let pushed := evalsToInTime_single
        (step_pushOutput first second symbol remaining output)
      let firstTwo := EvalsToInTime.trans (machine first second).step
        1 1 _ _ _ popped pushed
      let rest := induction (symbol :: output)
      let whole := EvalsToInTime.trans (machine first second).step
        2 (2 * remaining.length + 2) _ _ _ firstTwo rest
      simpa [whole, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

omit [Fintype InputSymbol] [Fintype FirstSymbol] [Fintype SecondSymbol]
    [Inhabited InputSymbol] [Inhabited FirstSymbol]
    [Inhabited SecondSymbol] in
theorem liftSecond_haltList_eq_outputAssembly
    (firstOutput : List (first.tm.Γ first.tm.k₁))
    (secondOutput : List (second.tm.Γ second.tm.k₁)) :
    liftSecondCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol
        (haltList first.tm firstOutput).stk
        (haltList second.tm secondOutput) =
      outputAssemblyCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol .drainFirstOutput
        (.firstOutput none) firstOutput secondOutput [] [] := by
  rfl

/-- Starting from the two canonical child halts, output assembly returns the
physical separated pair in linear time. -/
def outputAssemblyRun
    (firstOutput : List (first.tm.Γ first.tm.k₁))
    (secondOutput : List (second.tm.Γ second.tm.k₁)) :
    EvalsToInTime (machine first second).step
      (liftSecondCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol
        (haltList first.tm firstOutput).stk
        (haltList second.tm secondOutput))
      (some (haltList (machine first second)
        (physicalSeparated first second firstOutput secondOutput)))
      (4 * firstOutput.length + 4 * secondOutput.length + 7) := by
  have collected := collectOutputsRun first second firstOutput secondOutput
  have reversed := reverseOutputRun first second
    (physicalSeparated first second firstOutput secondOutput).reverse []
  let whole := EvalsToInTime.trans (machine first second).step
    (2 * firstOutput.length + 2 * secondOutput.length + 3)
    (2 * (physicalSeparated first second
      firstOutput secondOutput).reverse.length + 2)
    _ _ _ collected reversed
  rw [liftSecond_haltList_eq_outputAssembly
    first second firstOutput secondOutput]
  convert whole using 1
  · simp [physicalSeparated]
  · simp [physicalSeparated]
    omega

end

end TM2ForkMachine
end LeanTrominoes
