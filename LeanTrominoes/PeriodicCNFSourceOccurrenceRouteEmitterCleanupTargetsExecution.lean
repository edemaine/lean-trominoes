/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCleanupStageExecution

/-! # Cleanup of unary target tapes -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def targetCleanupData (data : TapeData) : TapeData :=
  { data with targetReverse := [], targets := [] }

def targetCleanupTime (data : TapeData) : Nat :=
  data.targetReverse.length + data.targets.length + 2

noncomputable def cleanupTargets_evalsInTime (cursor : Cursor)
    (data : TapeData) :
    EvalsToInTime machine.step (cleanupCfg .targetReverse cursor data)
      (some (cleanupCfg .clauseCount cursor (targetCleanupData data)))
      (targetCleanupTime data) := by
  let afterReverse := CleanupStage.targetReverse.cleared data
  let afterTargets := CleanupStage.targets.cleared afterReverse
  have reverseRun := cleanupStage_evalsInTime .targetReverse cursor
    data.targetReverse data rfl
  change EvalsToInTime machine.step
    (cleanupCfg .targetReverse cursor data)
    (some (cleanupCfg .targets cursor afterReverse))
    (data.targetReverse.length + 1) at reverseRun
  have targetsRun := cleanupStage_evalsInTime .targets cursor
    data.targets afterReverse (by rfl)
  change EvalsToInTime machine.step (cleanupCfg .targets cursor afterReverse)
    (some (cleanupCfg .clauseCount cursor afterTargets))
    (data.targets.length + 1) at targetsRun
  have whole := EvalsToInTime.trans machine.step
    (data.targetReverse.length + 1) (data.targets.length + 1)
    _ _ _ reverseRun targetsRun
  have afterTargetsEq : afterTargets = targetCleanupData data := by
    cases data
    rfl
  rw [afterTargetsEq] at whole
  convert whole using 1
  simp [targetCleanupTime]
  omega

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
