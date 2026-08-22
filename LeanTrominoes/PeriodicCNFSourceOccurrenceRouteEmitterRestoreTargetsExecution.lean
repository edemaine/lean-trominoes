/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterExecutionSupport
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRestoreSteps

/-! # Restoring the unary target stream -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def restoreTargets_evalsInTime (cursor : Cursor)
    (symbols : List UnarySymbol) (data : TapeData)
    (reverseEq : data.targetReverse = symbols) :
    EvalsToInTime machine.step (restoreTargetsCfg cursor data)
      (some (scanOccurrencesCfg cursor
        { data with
          targetReverse := []
          targets := symbols.reverse ++ data.targets }))
      (2 * symbols.length + 1) := by
  induction symbols generalizing data with
  | nil =>
      have step := step_restoreTargets_nil cursor data reverseEq
      simpa using oneStep step
  | cons symbol symbols induction =>
      let afterPop : TapeData :=
        { data with targetReverse := symbols }
      let nextData : TapeData :=
        { afterPop with targets := symbol :: data.targets }
      let popped := oneStep
        (step_restoreTargets_cons cursor data symbol symbols reverseEq)
      let pushed := oneStep
        (step_pushTargetForward cursor afterPop symbol)
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * symbols.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, afterPop, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
