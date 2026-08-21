/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ForkMachineComponentSteps

/-! # Bounded component executions inside the fork machine -/

noncomputable section

namespace LeanTrominoes
namespace TM2ForkMachine

open StateTransition Turing

private theorem iterate_none {Configuration : Type}
    (transition : Configuration → Option Configuration) (steps : Nat) :
    (flip bind transition)^[steps] none = none := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
      rw [Function.iterate_succ_apply]
      exact induction

private theorem lift_iterate
    {Source Target : Type}
    (source : Source → Option Source)
    (target : Target → Option Target) (lift : Source → Target)
    (stepLift : ∀ {before after}, source before = some after →
      target (lift before) = some (lift after)) :
    ∀ (steps : Nat) (before after : Source),
      (flip bind source)^[steps] (some before) = some after →
      (flip bind target)^[steps] (some (lift before)) =
        some (lift after) := by
  intro steps
  induction steps with
  | zero =>
      intro before after equality
      simp only [Function.iterate_zero, id_eq,
        Option.some.injEq] at equality ⊢
      subst after
      rfl
  | succ steps induction =>
      intro before after equality
      rw [Function.iterate_succ_apply] at equality ⊢
      cases firstStep : source before with
      | none =>
          change (flip bind source)^[steps] (source before) =
            some after at equality
          rw [firstStep, iterate_none] at equality
          cases equality
      | some middle =>
          change (flip bind source)^[steps] (source before) =
            some after at equality
          change (flip bind target)^[steps] (target (lift before)) =
            some (lift after)
          rw [stepLift firstStep]
          exact induction middle after (by simpa [firstStep] using equality)

/-- Lift a bounded first-component run without changing its counted number
of steps. -/
def liftFirstEvalsToInTime
    {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
    [Fintype InputSymbol] [Fintype FirstSymbol] [Fintype SecondSymbol]
    [Inhabited InputSymbol] [Inhabited FirstSymbol]
    [Inhabited SecondSymbol]
    {encodeInput : Input → List InputSymbol}
    {encodeFirst : FirstOutput → List FirstSymbol}
    {encodeSecond : SecondOutput → List SecondSymbol}
    {firstFunction : Input → FirstOutput}
    {secondFunction : Input → SecondOutput}
    (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
    (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction)
    (secondContents : ∀ stack, List (second.tm.Γ stack))
    {before after : first.tm.Cfg} {bound : Nat}
    (run : EvalsToInTime first.tm.step before (some after) bound) :
    EvalsToInTime (machine first second).step
      (liftFirstCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol secondContents before)
      (some (liftFirstCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol secondContents after)) bound where
  steps := run.steps
  evals_in_steps := lift_iterate first.tm.step
    (machine first second).step
    (liftFirstCfg first.tm second.tm
      InputSymbol FirstSymbol SecondSymbol secondContents)
    (liftFirst_step first second secondContents)
    run.steps before after run.evals_in_steps
  steps_le_m := run.steps_le_m

/-- Lift a bounded second-component run without changing its counted number
of steps. -/
def liftSecondEvalsToInTime
    {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
    [Fintype InputSymbol] [Fintype FirstSymbol] [Fintype SecondSymbol]
    [Inhabited InputSymbol] [Inhabited FirstSymbol]
    [Inhabited SecondSymbol]
    {encodeInput : Input → List InputSymbol}
    {encodeFirst : FirstOutput → List FirstSymbol}
    {encodeSecond : SecondOutput → List SecondSymbol}
    {firstFunction : Input → FirstOutput}
    {secondFunction : Input → SecondOutput}
    (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
    (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction)
    (firstContents : ∀ stack, List (first.tm.Γ stack))
    {before after : second.tm.Cfg} {bound : Nat}
    (run : EvalsToInTime second.tm.step before (some after) bound) :
    EvalsToInTime (machine first second).step
      (liftSecondCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol firstContents before)
      (some (liftSecondCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol firstContents after)) bound where
  steps := run.steps
  evals_in_steps := lift_iterate second.tm.step
    (machine first second).step
    (liftSecondCfg first.tm second.tm
      InputSymbol FirstSymbol SecondSymbol firstContents)
    (liftSecond_step first second firstContents)
    run.steps before after run.evals_in_steps
  steps_le_m := run.steps_le_m

end TM2ForkMachine
end LeanTrominoes
