/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCleanupStageExecution

/-! # Cleanup of input and occurrence tapes -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def occurrenceCleanupData (data : TapeData) : TapeData :=
  { data with input := [], occurrenceReverse := [], occurrences := [] }

def occurrenceCleanupTime (data : TapeData) : Nat :=
  data.input.length + data.occurrenceReverse.length +
    data.occurrences.length + 3

noncomputable def cleanupOccurrences_evalsInTime (cursor : Cursor)
    (data : TapeData) :
    EvalsToInTime machine.step (cleanupCfg .input cursor data)
      (some (cleanupCfg .targetReverse cursor (occurrenceCleanupData data)))
      (occurrenceCleanupTime data) := by
  let afterInput := CleanupStage.input.cleared data
  let afterReverse := CleanupStage.occurrenceReverse.cleared afterInput
  let afterOccurrences := CleanupStage.occurrences.cleared afterReverse
  have inputRun := cleanupStage_evalsInTime .input cursor data.input data rfl
  change EvalsToInTime machine.step (cleanupCfg .input cursor data)
    (some (cleanupCfg .occurrenceReverse cursor afterInput))
    (data.input.length + 1) at inputRun
  have reverseRun := cleanupStage_evalsInTime .occurrenceReverse cursor
    data.occurrenceReverse afterInput (by rfl)
  change EvalsToInTime machine.step
    (cleanupCfg .occurrenceReverse cursor afterInput)
    (some (cleanupCfg .occurrences cursor afterReverse))
    (data.occurrenceReverse.length + 1) at reverseRun
  have throughReverse := EvalsToInTime.trans machine.step
    (data.input.length + 1) (data.occurrenceReverse.length + 1)
    _ _ _ inputRun reverseRun
  have occurrencesRun := cleanupStage_evalsInTime .occurrences cursor
    data.occurrences afterReverse (by rfl)
  change EvalsToInTime machine.step
    (cleanupCfg .occurrences cursor afterReverse)
    (some (cleanupCfg .targetReverse cursor afterOccurrences))
    (data.occurrences.length + 1) at occurrencesRun
  have whole := EvalsToInTime.trans machine.step
    (data.occurrenceReverse.length + 1 + (data.input.length + 1))
    (data.occurrences.length + 1) _ _ _ throughReverse
    occurrencesRun
  have afterOccurrencesEq :
      afterOccurrences = occurrenceCleanupData data := by
    cases data
    rfl
  rw [afterOccurrencesEq] at whole
  convert whole using 1
  simp [occurrenceCleanupTime]
  omega

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
