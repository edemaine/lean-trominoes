/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapOutputSteps

/-! # Finalization executions of the end-delimited compiler map -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Computability StateTransition Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

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

/-- Discard an unterminated partial block. -/
def discardRun (blockReverse : List Source) (outputReverse : List Target) :
    EvalsToInTime (machine inner isEnd).step
      (discardCfg inner.tm Source Target blockReverse outputReverse)
      (some (reverseCfg inner.tm Source Target outputReverse []))
      (blockReverse.length + 1) := by
  induction blockReverse with
  | nil =>
      change EvalsToInTime (machine inner isEnd).step
        (discardCfg inner.tm Source Target [] outputReverse)
        (some (reverseCfg inner.tm Source Target outputReverse [])) 1
      let run : EvalsToInTime (machine inner isEnd).step
          (discardCfg inner.tm Source Target [] outputReverse)
          (some (reverseCfg inner.tm Source Target outputReverse [])) 1 :=
        evalsToInTime_single (step_discard_nil inner isEnd outputReverse)
      exact run
  | cons symbol remaining induction =>
      let first := evalsToInTime_single
        (step_discard_cons inner isEnd symbol remaining outputReverse)
      let rest := induction
      let whole := EvalsToInTime.trans (machine inner isEnd).step
        1 (remaining.length + 1) _ _ _ first rest
      simpa [Nat.add_assoc] using whole

/-- Reverse the accumulated output into forward order and halt. -/
def reverseRun (outputReverse output : List Target) :
    EvalsToInTime (machine inner isEnd).step
      (reverseCfg inner.tm Source Target outputReverse output)
      (some (haltCfg inner.tm Source Target
        (outputReverse.reverse ++ output)))
      (2 * outputReverse.length + 1) := by
  induction outputReverse generalizing output with
  | nil =>
      change EvalsToInTime (machine inner isEnd).step
        (reverseCfg inner.tm Source Target [] output)
        (some (haltCfg inner.tm Source Target output)) 1
      let run : EvalsToInTime (machine inner isEnd).step
          (reverseCfg inner.tm Source Target [] output)
          (some (haltCfg inner.tm Source Target output)) 1 :=
        evalsToInTime_single (step_reverse_nil inner isEnd output)
      exact run
  | cons symbol remaining induction =>
      let first := evalsToInTime_single
        (step_reverse_cons inner isEnd symbol remaining output)
      let second := evalsToInTime_single
        (step_pushFinal inner isEnd symbol remaining output)
      let firstTwo := EvalsToInTime.trans (machine inner isEnd).step
        1 1 _ _ _ first second
      let rest := induction (symbol :: output)
      let whole := EvalsToInTime.trans (machine inner isEnd).step
        2 (2 * remaining.length + 1) _ _ _ firstTwo rest
      simpa [List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc] using whole

theorem haltStacks_eq_haltList
    (output : List Target) :
    stackContents inner.tm Source Target [] []
        (emptyInnerStacks inner.tm) [] output =
      (haltList (machine inner isEnd) output).stk := by
  funext stack
  cases stack <;> simp [stackContents, emptyInnerStacks, haltList, machine]

theorem haltCfg_eq_haltList (output : List Target) :
    haltCfg inner.tm Source Target output =
      haltList (machine inner isEnd) output := by
  rw [haltCfg, haltStacks_eq_haltList inner isEnd output]
  rfl

/-- Discard a partial suffix, assemble the forward output, and reach the
canonical halt configuration. -/
def finalizeRun (blockReverse : List Source)
    (outputReverse : List Target) :
    EvalsToInTime (machine inner isEnd).step
      (discardCfg inner.tm Source Target blockReverse outputReverse)
      (some (haltList (machine inner isEnd) outputReverse.reverse))
      ((2 * outputReverse.length + 1) + (blockReverse.length + 1)) := by
  let discarded := discardRun inner isEnd blockReverse outputReverse
  let reversed := reverseRun inner isEnd outputReverse []
  let whole := EvalsToInTime.trans (machine inner isEnd).step
    (blockReverse.length + 1) (2 * outputReverse.length + 1)
    _ _ _ discarded reversed
  simp only [List.append_nil] at whole
  rw [haltCfg_eq_haltList inner isEnd outputReverse.reverse] at whole
  exact whole

end

end TM2EndDelimitedBlockMap
end LeanTrominoes
