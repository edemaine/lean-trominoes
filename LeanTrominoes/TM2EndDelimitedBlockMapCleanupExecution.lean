/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapCleanupMeasure

/-! # Complete cleanup execution of the end-delimited compiler map -/

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

/-- Cleanup visits the remaining finite stack indices, removes every cell,
and returns to collection.  Its counted time is linear in the remaining
population plus the number of indices still to visit. -/
def cleanupRun
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (position : Fin (Fintype.card inner.tm.K + 1))
    (input : List Source)
    (innerContents : ∀ stack, List (inner.tm.Γ stack))
    (outputReverse : List Target)
    (cleared : ClearedBefore inner.tm position innerContents) :
    EvalsToInTime (machine inner isEnd).step
      (cleanupCfg inner.tm Source Target position input innerContents
        outputReverse)
      (some (collectCfg inner.tm Source Target input []
        (emptyInnerStacks inner.tm) outputReverse))
      (cleanupMeasure inner.tm position innerContents + 1) := by
  cases selected : cleanupStack inner.tm position with
  | none =>
      have contentsEmpty :=
        innerContents_eq_empty_of_clearedBefore_finished inner.tm position
          innerContents cleared selected
      have positionEq :=
        cleanupStack_none_position inner.tm position selected
      let finishedRun : EvalsToInTime (machine inner isEnd).step
          (cleanupCfg inner.tm Source Target position input innerContents
            outputReverse)
          (some (collectCfg inner.tm Source Target input [] innerContents
            outputReverse)) 1 :=
        evalsToInTime_single
          (step_cleanup_none inner isEnd position input innerContents
            outputReverse selected)
      simpa [cleanupMeasure, innerPopulation, contentsEmpty,
        emptyInnerStacks, positionEq] using finishedRun
  | some stack =>
      have fits := cleanupStack_some_lt inner.tm position stack selected
      cases contentsEq : innerContents stack with
      | nil =>
          let first := evalsToInTime_single
            (step_cleanup_some_nil inner isEnd position stack input
              innerContents outputReverse selected contentsEq)
          have nextCleared := ClearedBefore.next inner.tm position stack
            innerContents cleared selected contentsEq
          have decreases := cleanupMeasure_next_lt inner.tm position
            innerContents fits
          let rest := cleanupRun inner isEnd
            (nextCleanupPosition inner.tm position) input innerContents
            outputReverse nextCleared
          let whole := EvalsToInTime.trans (machine inner isEnd).step
            1 (cleanupMeasure inner.tm
              (nextCleanupPosition inner.tm position) innerContents + 1)
            _ _ _ first rest
          have measureEq := cleanupMeasure_next_add_one inner.tm position
            innerContents fits
          simpa [measureEq] using whole
      | cons symbol tail =>
          let updated := @Function.update _ _ inner.tm.kDecidableEq
            innerContents stack tail
          let first := evalsToInTime_single
            (step_cleanup_some_cons inner isEnd position stack input
              innerContents symbol tail outputReverse selected contentsEq)
          have updatedCleared := ClearedBefore.update_current inner.tm
            position stack innerContents tail cleared selected
          have decreases := cleanupMeasure_update_lt inner.tm
            inner.tm.kDecidableEq position innerContents stack symbol tail
            contentsEq
          let rest := cleanupRun inner isEnd position input updated
            outputReverse updatedCleared
          let whole := EvalsToInTime.trans (machine inner isEnd).step
            1 (cleanupMeasure inner.tm position updated + 1)
            _ _ _ first rest
          have measureEq := cleanupMeasure_update_add_one inner.tm
            inner.tm.kDecidableEq position innerContents stack symbol tail
            contentsEq
          simpa [updated, measureEq] using whole
termination_by cleanupMeasure inner.tm position innerContents
decreasing_by
  · exact decreases
  · simpa only [updated] using decreases

end

end TM2EndDelimitedBlockMap
end LeanTrominoes
