/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCleanupGroupData

/-! # Cleanup of tagged-emitter counters and scratch tape -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def counterCleanup_evalsInTime (tag : Tag)
    (data : TapeData) :
    EvalsToInTime machine.step (cleanupCfg .clauseCount tag data)
      (some (cleanupCfg .outputReverse tag (counterCleanupData data)))
      (counterCleanupTime data) := by
  have clauseRun := cleanupStage_evalsInTime .clauseCount tag
    data.clauseCount data rfl
  have clauseRun' : EvalsToInTime machine.step
      (cleanupCfg .clauseCount tag data)
      (some (cleanupCfg .literalCount tag (afterCleanupClauseCount data)))
      (data.clauseCount.length + 1) := by
    change EvalsToInTime machine.step (cleanupCfg .clauseCount tag data)
      (some (cleanupCfg .literalCount tag (afterCleanupClauseCount data)))
      (data.clauseCount.length + 1) at clauseRun
    exact clauseRun
  have literalRun := cleanupStage_evalsInTime .literalCount tag
    data.literalCount (afterCleanupClauseCount data) rfl
  have literalRun' : EvalsToInTime machine.step
      (cleanupCfg .literalCount tag (afterCleanupClauseCount data))
      (some (cleanupCfg .linkIndex tag (afterCleanupLiteralCount data)))
      (data.literalCount.length + 1) := by
    change EvalsToInTime machine.step
      (cleanupCfg .literalCount tag (afterCleanupClauseCount data))
      (some (cleanupCfg .linkIndex tag (afterCleanupLiteralCount data)))
      (data.literalCount.length + 1) at literalRun
    exact literalRun
  have throughLiteral := EvalsToInTime.trans machine.step
    (data.clauseCount.length + 1) (data.literalCount.length + 1)
    _ _ _ clauseRun' literalRun'
  have linkRun := cleanupStage_evalsInTime .linkIndex tag data.linkIndex
    (afterCleanupLiteralCount data) rfl
  have linkRun' : EvalsToInTime machine.step
      (cleanupCfg .linkIndex tag (afterCleanupLiteralCount data))
      (some (cleanupCfg .scratch tag (afterCleanupLinkIndex data)))
      (data.linkIndex.length + 1) := by
    change EvalsToInTime machine.step
      (cleanupCfg .linkIndex tag (afterCleanupLiteralCount data))
      (some (cleanupCfg .scratch tag (afterCleanupLinkIndex data)))
      (data.linkIndex.length + 1) at linkRun
    exact linkRun
  have throughLink := EvalsToInTime.trans machine.step
    (data.literalCount.length + 1 + (data.clauseCount.length + 1))
    (data.linkIndex.length + 1) _ _ _ throughLiteral linkRun'
  have scratchRun := cleanupStage_evalsInTime .scratch tag data.scratch
    (afterCleanupLinkIndex data) rfl
  have scratchRun' : EvalsToInTime machine.step
      (cleanupCfg .scratch tag (afterCleanupLinkIndex data))
      (some (cleanupCfg .outputReverse tag (counterCleanupData data)))
      (data.scratch.length + 1) := by
    change EvalsToInTime machine.step
      (cleanupCfg .scratch tag (afterCleanupLinkIndex data))
      (some (cleanupCfg .outputReverse tag (counterCleanupData data)))
      (data.scratch.length + 1) at scratchRun
    exact scratchRun
  have whole := EvalsToInTime.trans machine.step
    (data.linkIndex.length + 1 +
      (data.literalCount.length + 1 + (data.clauseCount.length + 1)))
    (data.scratch.length + 1) _ _ _ throughLink scratchRun'
  simpa only [counterCleanupTime] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
