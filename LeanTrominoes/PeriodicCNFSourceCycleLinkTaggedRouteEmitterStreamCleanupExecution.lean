/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCleanupGroupData

/-! # Cleanup of tagged-emitter stream tapes -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def streamCleanup_evalsInTime (tag : Tag)
    (data : TapeData) :
    EvalsToInTime machine.step (cleanupCfg .input tag data)
      (some (cleanupCfg .clauseCount tag (streamCleanupData data)))
      (streamCleanupTime data) := by
  have inputRun := cleanupStage_evalsInTime .input tag data.input data rfl
  have inputRun' : EvalsToInTime machine.step
      (cleanupCfg .input tag data)
      (some (cleanupCfg .tagReverse tag (afterCleanupInput data)))
      (data.input.length + 1) := by
    change EvalsToInTime machine.step (cleanupCfg .input tag data)
      (some (cleanupCfg .tagReverse tag (afterCleanupInput data)))
      (data.input.length + 1) at inputRun
    exact inputRun
  have tagReverseRun := cleanupStage_evalsInTime .tagReverse tag
    data.tagReverse (afterCleanupInput data) rfl
  have tagReverseRun' : EvalsToInTime machine.step
      (cleanupCfg .tagReverse tag (afterCleanupInput data))
      (some (cleanupCfg .tags tag (afterCleanupTagReverse data)))
      (data.tagReverse.length + 1) := by
    change EvalsToInTime machine.step
      (cleanupCfg .tagReverse tag (afterCleanupInput data))
      (some (cleanupCfg .tags tag (afterCleanupTagReverse data)))
      (data.tagReverse.length + 1) at tagReverseRun
    exact tagReverseRun
  have throughTagReverse := EvalsToInTime.trans machine.step
    (data.input.length + 1) (data.tagReverse.length + 1)
    _ _ _ inputRun' tagReverseRun'
  have tagsRun := cleanupStage_evalsInTime .tags tag data.tags
    (afterCleanupTagReverse data) rfl
  have tagsRun' : EvalsToInTime machine.step
      (cleanupCfg .tags tag (afterCleanupTagReverse data))
      (some (cleanupCfg .targetReverse tag (afterCleanupTags data)))
      (data.tags.length + 1) := by
    change EvalsToInTime machine.step
      (cleanupCfg .tags tag (afterCleanupTagReverse data))
      (some (cleanupCfg .targetReverse tag (afterCleanupTags data)))
      (data.tags.length + 1) at tagsRun
    exact tagsRun
  have throughTags := EvalsToInTime.trans machine.step
    (data.tagReverse.length + 1 + (data.input.length + 1))
    (data.tags.length + 1) _ _ _ throughTagReverse tagsRun'
  have targetReverseRun := cleanupStage_evalsInTime .targetReverse tag
    data.targetReverse (afterCleanupTags data) rfl
  have targetReverseRun' : EvalsToInTime machine.step
      (cleanupCfg .targetReverse tag (afterCleanupTags data))
      (some (cleanupCfg .targets tag (afterCleanupTargetReverse data)))
      (data.targetReverse.length + 1) := by
    change EvalsToInTime machine.step
      (cleanupCfg .targetReverse tag (afterCleanupTags data))
      (some (cleanupCfg .targets tag (afterCleanupTargetReverse data)))
      (data.targetReverse.length + 1) at targetReverseRun
    exact targetReverseRun
  have throughTargetReverse := EvalsToInTime.trans machine.step
    (data.tags.length + 1 +
      (data.tagReverse.length + 1 + (data.input.length + 1)))
    (data.targetReverse.length + 1)
    _ _ _ throughTags targetReverseRun'
  have targetsRun := cleanupStage_evalsInTime .targets tag data.targets
    (afterCleanupTargetReverse data) rfl
  have targetsRun' : EvalsToInTime machine.step
      (cleanupCfg .targets tag (afterCleanupTargetReverse data))
      (some (cleanupCfg .clauseCount tag (streamCleanupData data)))
      (data.targets.length + 1) := by
    change EvalsToInTime machine.step
      (cleanupCfg .targets tag (afterCleanupTargetReverse data))
      (some (cleanupCfg .clauseCount tag (streamCleanupData data)))
      (data.targets.length + 1) at targetsRun
    exact targetsRun
  have whole := EvalsToInTime.trans machine.step
    (data.targetReverse.length + 1 +
      (data.tags.length + 1 +
        (data.tagReverse.length + 1 + (data.input.length + 1))))
    (data.targets.length + 1) _ _ _ throughTargetReverse targetsRun'
  simpa only [streamCleanupTime] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
