/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterCleanupExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterStreamCleanupExecution

/-! # Complete final cleanup for tagged cycle-link route emission -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def cleanupTime (data : TapeData) : Nat :=
  data.outputReverse.length + 1 +
    (counterCleanupTime (streamCleanupData data) + streamCleanupTime data)

noncomputable def cleanup_evalsInTime (tag : Tag) (data : TapeData) :
    EvalsToInTime machine.step (cleanupCfg .input tag data)
      (some (haltCfg data.output)) (cleanupTime data) := by
  have streams := streamCleanup_evalsInTime tag data
  have counters := counterCleanup_evalsInTime tag (streamCleanupData data)
  have throughCounters := EvalsToInTime.trans machine.step
    (streamCleanupTime data)
    (counterCleanupTime (streamCleanupData data))
    _ _ _ streams counters
  have outputRun := cleanupStage_evalsInTime .outputReverse tag
    data.outputReverse (counterCleanupData (streamCleanupData data)) rfl
  have outputRun' : EvalsToInTime machine.step
      (cleanupCfg .outputReverse tag
        (counterCleanupData (streamCleanupData data)))
      (some (haltCfg data.output)) (data.outputReverse.length + 1) := by
    change EvalsToInTime machine.step
      (cleanupCfg .outputReverse tag
        (counterCleanupData (streamCleanupData data)))
      (some (haltCfg data.output)) (data.outputReverse.length + 1)
      at outputRun
    exact outputRun
  have whole := EvalsToInTime.trans machine.step
    (counterCleanupTime (streamCleanupData data) + streamCleanupTime data)
    (data.outputReverse.length + 1) _ _ _ throughCounters outputRun'
  simpa only [cleanupTime] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
