/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterExecutionSupport
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRestoreSteps

/-! # Restoring the source-occurrence stream -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def restoreOccurrences_evalsInTime (cursor : Cursor)
    (tokens : List OccurrenceToken) (data : TapeData)
    (reverseEq : data.occurrenceReverse = tokens) :
    EvalsToInTime machine.step (restoreOccurrencesCfg cursor data)
      (some (restoreTargetsCfg cursor
        { data with
          occurrenceReverse := []
          occurrences := tokens.reverse ++ data.occurrences }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_restoreOccurrences_nil cursor data reverseEq
      simpa using oneStep step
  | cons token tokens induction =>
      let afterPop : TapeData :=
        { data with occurrenceReverse := tokens }
      let nextData : TapeData :=
        { afterPop with occurrences := token :: data.occurrences }
      let popped := oneStep
        (step_restoreOccurrences_cons cursor data token tokens reverseEq)
      let pushed := oneStep
        (step_pushOccurrenceForward cursor afterPop token)
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, afterPop, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
