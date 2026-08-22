/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapInnerSteps

/-! # Inner-machine executions of the end-delimited compiler map -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Computability StateTransition Turing

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

/-- Lift a bounded inner execution without changing its counted number of
steps or the surrounding input and accumulated output. -/
def liftInnerEvalsToInTime
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (input : List Source) (outputReverse : List Target)
    {before after : inner.tm.Cfg} {bound : Nat}
    (run : EvalsToInTime inner.tm.step before (some after) bound) :
    EvalsToInTime (machine inner isEnd).step
      (liftInnerCfg inner.tm Source Target input outputReverse before)
      (some (liftInnerCfg inner.tm Source Target input outputReverse after))
      bound where
  steps := run.steps
  evals_in_steps := lift_iterate inner.tm.step
    (machine inner isEnd).step
    (liftInnerCfg inner.tm Source Target input outputReverse)
    (liftInner_step inner isEnd input outputReverse)
    run.steps before after run.evals_in_steps
  steps_le_m := run.steps_le_m

end TM2EndDelimitedBlockMap
end LeanTrominoes
