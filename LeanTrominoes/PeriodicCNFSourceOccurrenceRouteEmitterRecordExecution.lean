/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordPrefixExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordSuffixExecution

/-! # One-record execution for source-occurrence route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def record_evalsInTime (cursor : Cursor) (data : TapeData)
    (targetCount : Nat) (remainingTargets : List UnarySymbol)
    (scratchEq : data.scratch = [])
    (targetsEq : data.targets =
      List.replicate targetCount .unit ++ .delimiter :: remainingTargets) :
    EvalsToInTime machine.step
      (beginRecordCfg cursor data)
      (some (scanOccurrencesCfg cursor
        (afterFinishedRecordData
          (afterRecordCounters (beginRecordData data))
          targetCount remainingTargets cursor.literalIndex
          cursor.currentNext cursor.anchorValue)))
      (recordTime data targetCount) := by
  have prefixRun := recordPrefix_evalsInTime cursor data scratchEq
  have counterTargetsEq :
      (afterRecordCounters (beginRecordData data)).targets =
        List.replicate targetCount .unit ++
          .delimiter :: remainingTargets := by
    simpa only [afterRecordCounters_targets, beginRecordData] using targetsEq
  have suffixRun := recordSuffix_evalsInTime cursor
    (afterRecordCounters (beginRecordData data)) targetCount remainingTargets
    counterTargetsEq
  have whole := EvalsToInTime.trans machine.step
    (recordCountersTime (beginRecordData data) + 1)
    (recordSuffixTime targetCount)
    (beginRecordCfg cursor data)
    (scanTargetCfg cursor (afterRecordCounters (beginRecordData data)))
    (some (scanOccurrencesCfg cursor
      (afterFinishedRecordData
        (afterRecordCounters (beginRecordData data))
        targetCount remainingTargets cursor.literalIndex
        cursor.currentNext cursor.anchorValue)))
    prefixRun suffixRun
  simpa only [recordTime] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
