/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapCleanupSteps
import LeanTrominoes.TM2EndDelimitedBlockMapDrainData

/-! # Output-draining executions of the end-delimited compiler map -/

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

/-- Drain an arbitrary inner output stack into the surrounding reverse-output
stack and enter cleanup. -/
def drainRun
    (symbols : List (inner.tm.Γ inner.tm.k₁))
    (input : List Source) (innerState : inner.tm.σ)
    (innerContents : ∀ stack, List (inner.tm.Γ stack))
    (outputReverse : List Target)
    (contentsEq : innerContents inner.tm.k₁ = symbols) :
    EvalsToInTime (machine inner isEnd).step
      (drainOutputCfg inner.tm Source Target input innerState innerContents
        outputReverse)
      (some (cleanupCfg inner.tm Source Target ⟨0, by omega⟩ input
        (clearInnerOutput inner.tm innerContents)
        ((symbols.map inner.outputAlphabet).reverse ++ outputReverse)))
      (2 * symbols.length + 1) := by
  induction symbols generalizing innerContents outputReverse with
  | nil =>
      have cleared := clearInnerOutput_eq_self inner.tm innerContents
        contentsEq
      change EvalsToInTime (machine inner isEnd).step
        (drainOutputCfg inner.tm Source Target input innerState innerContents
          outputReverse)
        (some (cleanupCfg inner.tm Source Target ⟨0, by omega⟩ input
          (clearInnerOutput inner.tm innerContents) outputReverse)) 1
      let run : EvalsToInTime (machine inner isEnd).step
          (drainOutputCfg inner.tm Source Target input innerState innerContents
            outputReverse)
          (some (cleanupCfg inner.tm Source Target ⟨0, by omega⟩ input
            innerContents outputReverse)) 1 :=
        evalsToInTime_single
          (step_drainOutput_nil inner isEnd input innerState innerContents
            outputReverse contentsEq)
      simpa only [cleared] using run
  | cons symbol remaining induction =>
      let updated := @Function.update _ _ inner.tm.kDecidableEq
        innerContents inner.tm.k₁ remaining
      have updatedEq : updated inner.tm.k₁ = remaining := by
        simp [updated]
      let first := evalsToInTime_single
        (step_drainOutput_cons inner isEnd symbol input innerState
          innerContents remaining outputReverse contentsEq)
      let second := evalsToInTime_single
        (step_pushOutput inner isEnd (inner.outputAlphabet symbol) input
          innerState updated outputReverse)
      let firstTwo := EvalsToInTime.trans (machine inner isEnd).step
        1 1 _ _ _ first second
      let rest := induction updated
        (inner.outputAlphabet symbol :: outputReverse) updatedEq
      let whole := EvalsToInTime.trans (machine inner isEnd).step
        2 (2 * remaining.length + 1) _ _ _ firstTwo rest
      simpa [updated, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc] using whole

omit [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target] in
@[simp] theorem liftInnerCfg_haltList
    (input : List Source) (outputReverse : List Target)
    (output : List (inner.tm.Γ inner.tm.k₁)) :
    liftInnerCfg inner.tm Source Target input outputReverse
        (haltList inner.tm output) =
      drainOutputCfg inner.tm Source Target input inner.tm.initialState
        (haltList inner.tm output).stk outputReverse := by
  rfl

/-- Drain a canonical halted inner machine. -/
def drainHaltRun
    (output : List (inner.tm.Γ inner.tm.k₁))
    (input : List Source) (outputReverse : List Target) :
    EvalsToInTime (machine inner isEnd).step
      (liftInnerCfg inner.tm Source Target input outputReverse
        (haltList inner.tm output))
      (some (cleanupCfg inner.tm Source Target ⟨0, by omega⟩ input
        (emptyInnerStacks inner.tm)
        ((output.map inner.outputAlphabet).reverse ++ outputReverse)))
      (2 * output.length + 1) := by
  have outputEq : (haltList inner.tm output).stk inner.tm.k₁ = output := by
    simp [haltList]
  let run := drainRun inner isEnd output input inner.tm.initialState
    (haltList inner.tm output).stk outputReverse outputEq
  simpa only [liftInnerCfg_haltList, clearInnerOutput_haltList] using run

/-- Decode a canonical inner encoding while draining it. -/
def drainEncodedHaltRun
    (output : List Target) (input : List Source)
    (outputReverse : List Target) :
    EvalsToInTime (machine inner isEnd).step
      (liftInnerCfg inner.tm Source Target input outputReverse
        (haltList inner.tm (output.map inner.outputAlphabet.invFun)))
      (some (cleanupCfg inner.tm Source Target ⟨0, by omega⟩ input
        (emptyInnerStacks inner.tm) (output.reverse ++ outputReverse)))
      (2 * output.length + 1) := by
  let run := drainHaltRun inner isEnd
    (output.map inner.outputAlphabet.invFun) input outputReverse
  simpa [List.map_map, Function.comp_def] using run

end

end TM2EndDelimitedBlockMap
end LeanTrominoes
