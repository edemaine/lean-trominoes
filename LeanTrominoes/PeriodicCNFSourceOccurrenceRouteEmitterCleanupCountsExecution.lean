/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCleanupStageExecution

/-! # Cleanup of total-count tapes -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def countCleanupData (data : TapeData) : TapeData :=
  { data with clauseCount := [], literalCount := [] }

def countCleanupTime (data : TapeData) : Nat :=
  data.clauseCount.length + data.literalCount.length + 2

noncomputable def cleanupCounts_evalsInTime (cursor : Cursor)
    (data : TapeData) :
    EvalsToInTime machine.step (cleanupCfg .clauseCount cursor data)
      (some (cleanupCfg .clauseIndex cursor (countCleanupData data)))
      (countCleanupTime data) := by
  let afterClauses := CleanupStage.clauseCount.cleared data
  let afterLiterals := CleanupStage.literalCount.cleared afterClauses
  have clausesRun := cleanupStage_evalsInTime .clauseCount cursor
    data.clauseCount data rfl
  change EvalsToInTime machine.step (cleanupCfg .clauseCount cursor data)
    (some (cleanupCfg .literalCount cursor afterClauses))
    (data.clauseCount.length + 1) at clausesRun
  have literalsRun := cleanupStage_evalsInTime .literalCount cursor
    data.literalCount afterClauses (by rfl)
  change EvalsToInTime machine.step
    (cleanupCfg .literalCount cursor afterClauses)
    (some (cleanupCfg .clauseIndex cursor afterLiterals))
    (data.literalCount.length + 1) at literalsRun
  have whole := EvalsToInTime.trans machine.step
    (data.clauseCount.length + 1) (data.literalCount.length + 1)
    _ _ _ clausesRun literalsRun
  have afterLiteralsEq : afterLiterals = countCleanupData data := by
    cases data
    rfl
  rw [afterLiteralsEq] at whole
  convert whole using 1
  simp [countCleanupTime]
  omega

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
