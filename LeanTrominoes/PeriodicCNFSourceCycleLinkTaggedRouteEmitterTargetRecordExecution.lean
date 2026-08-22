/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterLinkSteps
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordExecutionData
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSuffixSteps

/-! # Complete target-record execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def targetRecord_evalsInTime (tag : Tag)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (beginTargetRecordCfg tag data)
      (some (scanLinksCfg tag
        (afterIncrementLinkData
          (afterFinishedTargetData (afterTargetPrefixData data) tag))))
      (targetRecordTime data) := by
  have begin := oneStep (step_beginTargetRecord tag data)
  have begin' : EvalsToInTime machine.step
      (beginTargetRecordCfg tag data)
      (some (copyCounterCfg .targetVertexClause tag
        (beginTargetRecordData data))) 1 := by
    simpa only [beginTargetRecordData] using begin
  have beginScratchEq : (beginTargetRecordData data).scratch = [] := by
    simpa only [beginTargetRecordData] using scratchEq
  have counters := targetCounters_evalsInTime tag
    (beginTargetRecordData data) beginScratchEq
  have throughCounters := EvalsToInTime.trans machine.step
    1 (targetCountersTime (beginTargetRecordData data))
    _ _ _ begin' counters
  have finish := oneStep
    (step_finishTargetRecord tag (afterTargetPrefixData data))
  have finish' : EvalsToInTime machine.step
      (finishTargetRecordCfg tag (afterTargetPrefixData data))
      (some (incrementLinkCfg tag
        (afterFinishedTargetData (afterTargetPrefixData data) tag))) 1 := by
    simpa only [afterFinishedTargetData] using finish
  have throughFinish := EvalsToInTime.trans machine.step
    (targetCountersTime (beginTargetRecordData data) + 1) 1
    _ _ _ throughCounters finish'
  have increment := oneStep
    (step_incrementLink tag
      (afterFinishedTargetData (afterTargetPrefixData data) tag))
  have increment' : EvalsToInTime machine.step
      (incrementLinkCfg tag
        (afterFinishedTargetData (afterTargetPrefixData data) tag))
      (some (scanLinksCfg tag
        (afterIncrementLinkData
          (afterFinishedTargetData (afterTargetPrefixData data) tag)))) 1 := by
    simpa only [afterIncrementLinkData] using increment
  have whole := EvalsToInTime.trans machine.step
    (1 + (targetCountersTime (beginTargetRecordData data) + 1)) 1
    _ _ _ throughFinish increment'
  simpa only [targetRecordTime, afterTargetPrefixData] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
