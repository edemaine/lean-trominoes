/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterExecutionSupport
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterParseRightSteps

/-! # Execution of right-input parsing for source-occurrence route emission -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def scanRight_evalsInTime (cursor : Cursor) (symbols : List UnarySymbol)
    (data : TapeData) (inputEq : data.input = symbols.map .right) :
    EvalsToInTime machine.step (scanRightCfg cursor data)
      (some (restoreOccurrencesCfg cursor
        { data with
          input := []
          targetReverse := symbols.reverse ++ data.targetReverse }))
      (2 * symbols.length + 1) := by
  induction symbols generalizing data with
  | nil =>
      have step := step_scanRight_nil cursor data (by simpa using inputEq)
      simpa using oneStep step
  | cons symbol symbols induction =>
      have inputHead : data.input = .right symbol :: symbols.map .right := by
        simpa [List.map_cons] using inputEq
      let afterPop : TapeData :=
        { data with input := symbols.map .right }
      let nextData : TapeData :=
        { afterPop with
          targetReverse := symbol :: data.targetReverse }
      let popped := oneStep
        (step_scanRight_right cursor data symbol
          (symbols.map .right) inputHead)
      let pushed := oneStep
        (step_pushTargetReverse cursor afterPop symbol)
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * symbols.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, afterPop, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
