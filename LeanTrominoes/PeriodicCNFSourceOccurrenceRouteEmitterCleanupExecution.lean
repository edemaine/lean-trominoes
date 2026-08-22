/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCleanupCountsExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCleanupIndicesExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCleanupOccurrencesExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCleanupTargetsExecution

/-! # Complete final cleanup for source-occurrence route emission -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def cleanupTime (data : TapeData) : Nat :=
  data.input.length + data.occurrenceReverse.length +
    data.occurrences.length + data.targetReverse.length +
    data.targets.length + data.clauseCount.length +
    data.literalCount.length + data.clauseIndex.length +
    data.edgeIndex.length + data.scratch.length +
    data.outputReverse.length + 11

noncomputable def cleanup_evalsInTime (cursor : Cursor) (data : TapeData) :
    EvalsToInTime machine.step (cleanupCfg .input cursor data)
      (some (haltCfg initialCursor data.output)) (cleanupTime data) := by
  let afterOccurrences := occurrenceCleanupData data
  let afterTargets := targetCleanupData afterOccurrences
  let afterCounts := countCleanupData afterTargets
  let afterIndices := indexCleanupData afterCounts
  have occurrencesRun := cleanupOccurrences_evalsInTime cursor data
  have targetsRun := cleanupTargets_evalsInTime cursor afterOccurrences
  have throughTargets := EvalsToInTime.trans machine.step
    (occurrenceCleanupTime data) (targetCleanupTime afterOccurrences)
    _ _ _ occurrencesRun targetsRun
  have countsRun := cleanupCounts_evalsInTime cursor afterTargets
  have throughCounts := EvalsToInTime.trans machine.step
    (targetCleanupTime afterOccurrences + occurrenceCleanupTime data)
    (countCleanupTime afterTargets) _ _ _ throughTargets countsRun
  have indicesRun := cleanupIndices_evalsInTime cursor afterCounts
  have throughIndices := EvalsToInTime.trans machine.step
    (countCleanupTime afterTargets +
      (targetCleanupTime afterOccurrences + occurrenceCleanupTime data))
    (indexCleanupTime afterCounts) _ _ _ throughCounts indicesRun
  have outputRun := cleanupStage_evalsInTime .outputReverse cursor
    data.outputReverse afterIndices (by rfl)
  have whole := EvalsToInTime.trans machine.step
    (indexCleanupTime afterCounts +
      (countCleanupTime afterTargets +
        (targetCleanupTime afterOccurrences + occurrenceCleanupTime data)))
    (data.outputReverse.length + 1) _ _ _ throughIndices outputRun
  convert whole using 1
  · cases data
    rfl
  · simp [cleanupTime, occurrenceCleanupTime, targetCleanupTime,
      countCleanupTime, indexCleanupTime, afterOccurrences, afterTargets,
      afterCounts, occurrenceCleanupData, targetCleanupData,
      countCleanupData]
    omega

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
