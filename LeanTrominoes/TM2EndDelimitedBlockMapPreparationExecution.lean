/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapInnerSteps
import LeanTrominoes.TM2EndDelimitedBlockMapPreparationData

/-! # Input-preparation executions of the end-delimited compiler map -/

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

/-- Transfer an arbitrary reversed source word onto the inner input stack and
enter the inner machine. -/
def prepareRun
    (symbols input : List Source)
    (innerContents : ∀ stack, List (inner.tm.Γ stack))
    (outputReverse : List Target) :
    EvalsToInTime (machine inner isEnd).step
      (prepareCfg inner.tm Source Target input symbols innerContents
        outputReverse)
      (some (liftInnerCfg inner.tm Source Target input outputReverse
        ⟨some inner.tm.main, inner.tm.initialState,
          transferredContents inner.tm inner.inputAlphabet.invFun symbols
            innerContents⟩))
      (2 * symbols.length + 1) := by
  induction symbols generalizing innerContents with
  | nil =>
      change EvalsToInTime (machine inner isEnd).step
        (prepareCfg inner.tm Source Target input [] innerContents
          outputReverse)
        (some (liftInnerCfg inner.tm Source Target input outputReverse
          ⟨some inner.tm.main, inner.tm.initialState, innerContents⟩)) 1
      let run : EvalsToInTime (machine inner isEnd).step
          (prepareCfg inner.tm Source Target input [] innerContents
            outputReverse)
          (some (liftInnerCfg inner.tm Source Target input outputReverse
            ⟨some inner.tm.main, inner.tm.initialState, innerContents⟩)) 1 :=
        evalsToInTime_single
          (step_prepare_nil inner isEnd input innerContents outputReverse)
      exact run
  | cons symbol remaining induction =>
      let updated := @Function.update _ _ inner.tm.kDecidableEq
        innerContents inner.tm.k₀
          (inner.inputAlphabet.invFun symbol ::
            innerContents inner.tm.k₀)
      let first := evalsToInTime_single
        (step_prepare_cons inner isEnd symbol input remaining
          innerContents outputReverse)
      let second := evalsToInTime_single
        (step_pushInner inner isEnd symbol input remaining
          innerContents outputReverse)
      let firstTwo := EvalsToInTime.trans (machine inner isEnd).step
        1 1 _ _ _ first second
      let rest := induction updated
      let whole := EvalsToInTime.trans (machine inner isEnd).step
        2 (2 * remaining.length + 1) _ _ _ firstTwo rest
      simpa [updated, transferredContents, Nat.mul_add,
        Nat.add_assoc] using whole

/-- A complete reversed block enters the inner machine in its canonical
`initList` configuration. -/
def prepareBlockRun
    (block input : List Source) (outputReverse : List Target) :
    EvalsToInTime (machine inner isEnd).step
      (prepareCfg inner.tm Source Target input block.reverse
        (emptyInnerStacks inner.tm) outputReverse)
      (some (liftInnerCfg inner.tm Source Target input outputReverse
        (initList inner.tm
          (block.map inner.inputAlphabet.invFun))))
      (2 * block.length + 1) := by
  let run := prepareRun inner isEnd block.reverse input
    (emptyInnerStacks inner.tm) outputReverse
  simpa only [List.length_reverse,
    transferredCfg_reverse_empty_eq_initList] using run

end

end TM2EndDelimitedBlockMap
end LeanTrominoes
