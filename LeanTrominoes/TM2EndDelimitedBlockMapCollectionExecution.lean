/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapBoundarySteps

/-! # Input-collection executions of the end-delimited compiler map -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Computability StateTransition Turing

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

variable {Input Output Source Target : Type}
variable [Fintype Source] [Fintype Target]
variable [Inhabited Source] [Inhabited Target]
variable {encodeInput : Input → List Source}
variable {encodeOutput : Output → List Target}
variable {function : Input → Output}
variable (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
variable (isEnd : Source → Bool)

/-- Collect a delimiter-free prefix and its terminating symbol, leaving the
complete reversed block ready for transfer to the inner input stack. -/
def collectCompleteRun
    (body : List Source) (ending : Source) (rest blockReverse : List Source)
    (outputReverse : List Target)
    (continues : ∀ symbol ∈ body, isEnd symbol = false)
    (ends : isEnd ending = true) :
    EvalsToInTime (machine inner isEnd).step
      (collectCfg inner.tm Source Target
        (body ++ ending :: rest) blockReverse
        (emptyInnerStacks inner.tm) outputReverse)
      (some (prepareCfg inner.tm Source Target rest
        (ending :: body.reverse ++ blockReverse)
        (emptyInnerStacks inner.tm) outputReverse))
      (2 * body.length + 2) := by
  induction body generalizing blockReverse with
  | nil =>
      let first := evalsToInTime_single
        (step_collect_cons inner isEnd ending rest blockReverse outputReverse)
      let second := evalsToInTime_single
        (step_pushBlock_end inner isEnd ending rest blockReverse
          outputReverse ends)
      let whole := EvalsToInTime.trans (machine inner isEnd).step
        1 1 _ _ _ first second
      change EvalsToInTime (machine inner isEnd).step
        (collectCfg inner.tm Source Target (ending :: rest) blockReverse
          (emptyInnerStacks inner.tm) outputReverse)
        (some (prepareCfg inner.tm Source Target rest
          (ending :: blockReverse) (emptyInnerStacks inner.tm)
          outputReverse)) 2
      exact whole
  | cons symbol tail induction =>
      have symbolContinues : isEnd symbol = false :=
        continues symbol (by simp)
      have tailContinues : ∀ other ∈ tail, isEnd other = false := by
        intro other member
        exact continues other (by simp [member])
      let first := evalsToInTime_single
        (step_collect_cons inner isEnd symbol
          (tail ++ ending :: rest) blockReverse outputReverse)
      let second := evalsToInTime_single
        (step_pushBlock_continues inner isEnd symbol
          (tail ++ ending :: rest) blockReverse outputReverse
          symbolContinues)
      let firstTwo := EvalsToInTime.trans (machine inner isEnd).step
        1 1 _ _ _ first second
      let remaining := induction (symbol :: blockReverse) tailContinues
      let whole := EvalsToInTime.trans (machine inner isEnd).step
        2 (2 * tail.length + 2) _ _ _ firstTwo remaining
      simpa [List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc] using whole

/-- Consume a delimiter-free suffix and enter the discard phase at end of
input. -/
def collectPartialRun
    (body blockReverse : List Source) (outputReverse : List Target)
    (continues : ∀ symbol ∈ body, isEnd symbol = false) :
    EvalsToInTime (machine inner isEnd).step
      (collectCfg inner.tm Source Target body blockReverse
        (emptyInnerStacks inner.tm) outputReverse)
      (some (discardCfg inner.tm Source Target
        (body.reverse ++ blockReverse) outputReverse))
      (2 * body.length + 1) := by
  induction body generalizing blockReverse with
  | nil =>
      change EvalsToInTime (machine inner isEnd).step
        (collectCfg inner.tm Source Target [] blockReverse
          (emptyInnerStacks inner.tm) outputReverse)
        (some (discardCfg inner.tm Source Target blockReverse
          outputReverse)) 1
      let run : EvalsToInTime (machine inner isEnd).step
          (collectCfg inner.tm Source Target [] blockReverse
            (emptyInnerStacks inner.tm) outputReverse)
          (some (discardCfg inner.tm Source Target blockReverse
            outputReverse)) 1 :=
        evalsToInTime_single
          (step_collect_nil inner isEnd blockReverse outputReverse)
      exact run
  | cons symbol tail induction =>
      have symbolContinues : isEnd symbol = false :=
        continues symbol (by simp)
      have tailContinues : ∀ other ∈ tail, isEnd other = false := by
        intro other member
        exact continues other (by simp [member])
      let first := evalsToInTime_single
        (step_collect_cons inner isEnd symbol tail blockReverse outputReverse)
      let second := evalsToInTime_single
        (step_pushBlock_continues inner isEnd symbol tail blockReverse
          outputReverse symbolContinues)
      let firstTwo := EvalsToInTime.trans (machine inner isEnd).step
        1 1 _ _ _ first second
      let remaining := induction (symbol :: blockReverse) tailContinues
      let whole := EvalsToInTime.trans (machine inner isEnd).step
        2 (2 * tail.length + 1) _ _ _ firstTwo remaining
      simpa [List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc] using whole

end

end TM2EndDelimitedBlockMap
end LeanTrominoes
