/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapFullData
import LeanTrominoes.TM2EndDelimitedBlockMapFinalizationExecution

/-! # Complete executions of the end-delimited compiler map -/

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

variable {Source Target : Type}
variable [Fintype Source] [Fintype Target]
variable [Inhabited Source] [Inhabited Target]
variable {function : List Source → List Target}
variable (inner : TM2ComputableInPolyTime id id function)
variable (isEnd : Source → Bool)

/-- Process every complete block remaining in the input, then discard the
unterminated suffix and halt with the accumulated output in forward order.
-/
def mapRun
    (input blockReverse : List Source) (outputReverse : List Target) :
    EvalsToInTime (machine inner isEnd).step
      (collectCfg inner.tm Source Target input blockReverse
        (emptyInnerStacks inner.tm) outputReverse)
      (some (haltList (machine inner isEnd)
        (outputReverse.reverse ++
          (blocksAux isEnd blockReverse input).flatMap function)))
      (mapRunTime inner isEnd input blockReverse outputReverse) := by
  cases input with
  | nil =>
      let first : EvalsToInTime (machine inner isEnd).step
          (collectCfg inner.tm Source Target [] blockReverse
            (emptyInnerStacks inner.tm) outputReverse)
          (some (discardCfg inner.tm Source Target blockReverse
            outputReverse)) 1 :=
        evalsToInTime_single
          (step_collect_nil inner isEnd blockReverse outputReverse)
      let rest := finalizeRun inner isEnd blockReverse outputReverse
      let whole := EvalsToInTime.trans (machine inner isEnd).step
        1 ((2 * outputReverse.length + 1) +
          (blockReverse.length + 1)) _ _ _ first rest
      simpa [mapRunTime, blocksAux] using whole
  | cons symbol remaining =>
      let first := evalsToInTime_single
        (step_collect_cons inner isEnd symbol remaining blockReverse
          outputReverse)
      cases ends : isEnd symbol with
      | false =>
          let second := evalsToInTime_single
            (step_pushBlock_continues inner isEnd symbol remaining
              blockReverse outputReverse ends)
          let firstTwo := EvalsToInTime.trans (machine inner isEnd).step
            1 1 _ _ _ first second
          let rest := mapRun remaining (symbol :: blockReverse)
            outputReverse
          let whole := EvalsToInTime.trans (machine inner isEnd).step
            2 (mapRunTime inner isEnd remaining
              (symbol :: blockReverse) outputReverse)
            _ _ _ firstTwo rest
          simpa [mapRunTime, blocksAux, ends] using whole
      | true =>
          let block := (symbol :: blockReverse).reverse
          let second := evalsToInTime_single
            (step_pushBlock_end inner isEnd symbol remaining blockReverse
              outputReverse ends)
          let firstTwo := EvalsToInTime.trans (machine inner isEnd).step
            1 1 _ _ _ first second
          let rawBlockRun := completeBlockRun inner isEnd block remaining
            outputReverse
          have blockExecution : EvalsToInTime (machine inner isEnd).step
              (prepareCfg inner.tm Source Target remaining
                (symbol :: blockReverse) (emptyInnerStacks inner.tm)
                outputReverse)
              (some (collectCfg inner.tm Source Target remaining []
                (emptyInnerStacks inner.tm)
                ((function block).reverse ++ outputReverse)))
              (blockRunTime inner block) := by
            simpa [block] using rawBlockRun
          let throughBlock := EvalsToInTime.trans
            (machine inner isEnd).step 2 (blockRunTime inner block)
            _ _ _ firstTwo blockExecution
          let rest := mapRun remaining []
            ((function block).reverse ++ outputReverse)
          let whole := EvalsToInTime.trans (machine inner isEnd).step
            (blockRunTime inner block + 2)
            (mapRunTime inner isEnd remaining []
              ((function block).reverse ++ outputReverse))
            _ _ _ throughBlock rest
          simpa [mapRunTime, blocksAux, ends, block,
            List.reverse_append, List.append_assoc] using whole
termination_by input.length

/-- The wrapper computes the semantic end-delimited block map with the exact
recursive time bound above. -/
def machineRun (input : List Source) :
    EvalsToInTime (machine inner isEnd).step
      (initList (machine inner isEnd) input)
      (some (haltList (machine inner isEnd)
        (mappedOutput isEnd function input)))
      (mapRunTime inner isEnd input [] []) := by
  let run := mapRun inner isEnd input [] []
  rw [collectCfg_eq_initList inner isEnd input] at run
  simp only [List.reverse_nil, List.nil_append] at run
  change EvalsToInTime (machine inner isEnd).step
    (initList (machine inner isEnd) input)
    (some (haltList (machine inner isEnd)
      ((blocksAux isEnd [] input).flatMap function)))
    (mapRunTime inner isEnd input [] [])
  exact run

end

end TM2EndDelimitedBlockMap
end LeanTrominoes
