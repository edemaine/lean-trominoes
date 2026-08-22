/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCleanupStageExecution

/-! # Cleanup of index and scratch tapes -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def indexCleanupData (data : TapeData) : TapeData :=
  { data with clauseIndex := [], edgeIndex := [], scratch := [] }

def indexCleanupTime (data : TapeData) : Nat :=
  data.clauseIndex.length + data.edgeIndex.length + data.scratch.length + 3

noncomputable def cleanupIndices_evalsInTime (cursor : Cursor)
    (data : TapeData) :
    EvalsToInTime machine.step (cleanupCfg .clauseIndex cursor data)
      (some (cleanupCfg .outputReverse cursor (indexCleanupData data)))
      (indexCleanupTime data) := by
  let afterClause := CleanupStage.clauseIndex.cleared data
  let afterEdge := CleanupStage.edgeIndex.cleared afterClause
  let afterScratch := CleanupStage.scratch.cleared afterEdge
  have clauseRun := cleanupStage_evalsInTime .clauseIndex cursor
    data.clauseIndex data rfl
  change EvalsToInTime machine.step (cleanupCfg .clauseIndex cursor data)
    (some (cleanupCfg .edgeIndex cursor afterClause))
    (data.clauseIndex.length + 1) at clauseRun
  have edgeRun := cleanupStage_evalsInTime .edgeIndex cursor
    data.edgeIndex afterClause (by rfl)
  change EvalsToInTime machine.step (cleanupCfg .edgeIndex cursor afterClause)
    (some (cleanupCfg .scratch cursor afterEdge))
    (data.edgeIndex.length + 1) at edgeRun
  have throughEdge := EvalsToInTime.trans machine.step
    (data.clauseIndex.length + 1) (data.edgeIndex.length + 1)
    _ _ _ clauseRun edgeRun
  have scratchRun := cleanupStage_evalsInTime .scratch cursor
    data.scratch afterEdge (by rfl)
  change EvalsToInTime machine.step (cleanupCfg .scratch cursor afterEdge)
    (some (cleanupCfg .outputReverse cursor afterScratch))
    (data.scratch.length + 1) at scratchRun
  have whole := EvalsToInTime.trans machine.step
    (data.edgeIndex.length + 1 + (data.clauseIndex.length + 1))
    (data.scratch.length + 1) _ _ _ throughEdge scratchRun
  have afterScratchEq : afterScratch = indexCleanupData data := by
    cases data
    rfl
  rw [afterScratchEq] at whole
  convert whole using 1
  simp [indexCleanupTime]
  omega

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
